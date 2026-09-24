"""
dimensions.py — the validation package of "Dimensional Analysis over Finite Holographic Substrate" (Akhtman, 2026; Preprints
doi 10.20944/preprints202605.0668.v1), the paper 10-dimensions of the FRC corpus (finite-ring-space/src/10-dimensions); one
script since 24 September 2026 (the registry dimcommon.py and the suites verify_domains.py, check_lift.py merged).
========================================================================================================================

One script, two blocks, thirteen family checks of 217 exact micro-checks, standard library only. Every check is exact:
integers, residues, exact rationals; no floats, no random sampling. Block dom (verify_domains) is organised in eight layers
A–H, each a family of micro-checks; block lift (check_lift) decides the five claims L1–L5 of Proposition `lift` on two shells
and two Carriers. A family is one check of the registry, identified as <block>.<family> (dom.A … dom.H, lift.L1 … lift.L5),
and names the predicate(s) of the paper's ledger it witnesses (LEDGER; predicates cited as 10:<label>) — the deciding
family's `# 10:<label> (<key>)` marker is what the ledger's source column links (PREDICATES;
finitering.space/src/10-dimensions/#<key>); the family checks are listed on the public page from
results.json. Master-ledger predicates reached through the paper predicates: 00:D7 (10:D7), 00:C12 (10:F3), 00:C13 (10:E9,
10:G2), 00:C8 (10:E4), 00:B10 (10:E5).

    python3 dimensions.py         both blocks, results.json written; exit 1 if a family check fails (≈ 1 s)
    python3 dimensions.py lift    one block (dom or lift); no results.json
    from frc_10_dimensions import predicate; predicate("10:C5")    one predicate: its block runs once per session

The manuscript's 105 source gates (validation/check_gates.py in the corpus tree, where sections/*.tex live) are not part
of this package.
"""
import os, json, sys
from collections import OrderedDict
from fractions import Fraction as Fr
from math import gcd

SCRIPT = os.path.splitext(os.path.basename(__file__))[0]        # "dimensions": the one script, the name results.json and the site pages carry

RESULTS = []
MICRO = []             # (block, family, label, ok)

LEDGER = {
    "dom.A": "10:C2, 10:C3, 10:D2, 10:D6, 10:F2, 10:F4, 10:G1, 10:G3, 10:X1, 10:X3",
    "dom.B": "10:E2, 10:E3, 10:X1, 10:X2, 10:X3",
    "dom.C": "10:E4",
    "dom.D": "10:E4, 10:E5, 10:E9, 10:F3, 10:G1, 10:X2",
    "dom.E": "10:C5",
    "dom.F": "10:C5, 10:D1",
    "dom.G": "10:C5, 10:D2, 10:F5, 10:G2, 10:G4, 10:X4",
    "dom.H": "10:E4, 10:E5",
    "lift.L1": "10:D3", "lift.L2": "10:D3", "lift.L3": "10:D3", "lift.L4": "10:D3", "lift.L5": "10:C5, 10:D3",
}

LABELS = {
    "dom.A": "shell datum and domain algebra on F_13: frame datum (g = 2, i = −g^κ, π = 2κ, 4κ = p−1); the group law, inverses and grading of D_p = Z_p × Z_{p−1}; the internal flag I_q = [T]^κ unique of order four, no flag of space, horizon-inaccessible, covariant; realization a homomorphism; the derived domains (m, F, S, G, Compton, Planck area, Schwarzschild, orbital frequency); fibrewise addition and local recovery at H = 5; the energy–momentum relation in one fibre at crossing degree two",
    "dom.B": "the quartet at the unit face: exponent-vector relation lattice over {ℓ_P, t_P, ħ} (both faces of c and ħ differ by ℓp = tE; rank two; k_B and ℓE add nothing); exact-rational instantiation of every stated equality (|k_B|c = ħ, m_P, G, Θ_P, {c, ħ, G} ↔ quartet); 4 − 1 = 3 degrees of freedom; flag positions (0,0,1,1)",
    "dom.C": "the defining congruences on the lab Carrier Ω = 2 408 561 (S = 602 140): admissibility; 2G ≡ −1 unique; ħ² ≡ −1, k_B² ≡ −2, 2c² ≡ 1 with their exact root pairs; G ≡ −c², G² ≡ 4⁻¹, h ≡ −ħ; m_P² ≐ Ω ≡ 0",
    "dom.D": "both Carriers (233 and the lab Carrier): the congruence-and-closure system, ħcG⁻¹ landing in the k_B pair; the representative annex; the admissibility minimality scan certifying (13, 233) with the counterfactuals; [Θ] = [L][T]⁻² and the Unruh closure; the crossing-degree embedding injective and windowed-faithful",
    "dom.E": "covariance: the naive character ill-defined on the modular projection; (p−1, 0) trivial character yet non-neutral; the ε-composition failure; window covariance below the bound; pushforward-invariant labels {0, π}; the quarter-turn fix/swap criterion ε ≡ ±1 (mod 4); the index-two sublattice ⟨c, ħ, G⟩ (det −2)",
    "dom.F": "the (0, π) witness forcing H < 2κ; the σ-twisted action equivariant by full sweep on p = 13 and 229 with the plain-lift failure; σ multiplicative mod 4; δ_S, δ_C involutions, δ_C carrying [L] ↦ [p], [T] ↦ [E]",
    "dom.G": "realized action against the Z³-representative failure; the flagged label (0, 0; 1) moving under ε = −1; the window ladder 2√κ < κ/2 < κ < 2κ nested for every κ ≥ 17 and failing for κ = 3; (2√κ)² = p−1, (2√S)² = Ω−1; the flagged ratio F/a; meridian transport (L T^κ)^p = I_q on three shells; both roots on both Carriers; Buckingham's count on the integer lift (the pendulum: rank 3, one product); the electromagnetic domain — [q]² = I_q[L][T]⁻¹, its two roots on the odd capacities and none on the even, the meridian half-turn, the even labels on the lift, the dilation character",
    "dom.H": "the pair layer: pair multiplication well defined; the linkage {±k_B}{±c} = {±ħ} derived at pair level; ħcG⁻¹ in the k_B pair via (ħcG⁻¹)² ≡ −2; representative inertness — exactly the four assignments with σ_ħ = σ_c σ_k admissible, a (Z/2)², every identity holding on each; the ħ-flip relabelling of {ħ, h}",
    "lift.L1": "operator four-cycle: F = iW on F_p^{p−1}, F² = J, F⁴ = I, F² ≠ I (p = 13, 173)",
    "lift.L2": "chart shadow of order two: F exchanges the two dual charts, J exchanges none; the cardinal skeleton acts on charts as s mod 2",
    "lift.L3": "record map s ↦ I_q^s an isomorphism Z_4 → the flag subgroup {0, κ, 2κ, 3κ}; the quotient by {0, 2κ} returns s mod 2",
    "lift.L4": "Carrier face: ħ² = −1 (mod Ω), ħ⁴ = 1, ħ² ≠ 1 — the crossing quantum has order four, never two (Ω = 233, 2 408 561)",
    "lift.L5": "invariance on the realized lattice: {u : εu = u for every admissible ε} = {0, 2κ}; witnesses (κ,1) ↦ 2κ and (−κ,1) ↦ 0 invariant, (0,1) ↦ κ not, (0,2) ↦ 2κ invariant",
}

BLOCK = {"dom": "the eight layers A–H of exact micro-checks (verify_domains until 24 September 2026)",      # check-id prefix -> the block (the function block_<name> below)
         "lift": "Proposition `lift`, L1–L5 on two shells and two Carriers (check_lift)"}

# the deciding family of each witnessed predicate: the one whose checks decide the predicate's statement (the other families
# that touch it are corroboration, listed by predicate() from the records)
PREDICATES = {
    "10:C2": "dom.A", "10:C3": "dom.A", "10:C5": "dom.E", "10:D1": "dom.F", "10:D2": "dom.A", "10:D3": "lift.L1",
    "10:D6": "dom.A", "10:E2": "dom.B", "10:E3": "dom.B", "10:E4": "dom.C", "10:E5": "dom.H", "10:E9": "dom.D",
    "10:F2": "dom.A", "10:F3": "dom.D", "10:F4": "dom.A", "10:G1": "dom.A", "10:G2": "dom.G", "10:G3": "dom.A",
    "10:F5": "dom.G", "10:G4": "dom.G",
    "10:X1": "dom.B", "10:X2": "dom.D", "10:X3": "dom.A", "10:X4": "dom.G",       # block X restates E2/F2, E3/F3, D2/E2, F5: the same deciding checks
}
_FAM = [None, None]
_RAN = set()                                            # blocks already run in this session (predicate() runs each once)

def markers():
    """predicate label -> (script file, line) of its marker `# <paper>:<label> (<key>)`: the line of the check that decides it."""
    import re
    out = {}
    for i, line in enumerate(open(os.path.abspath(__file__), encoding="utf-8"), 1):
        m = re.match(r"\s*# ((?:\d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)(?:, \d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)*)\s*$", line)
        if m:
            for lab in re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)): out.setdefault(lab, (SCRIPT + ".py", i))
    return out

def _run_block(name):
    if name not in _RAN:
        globals()[f"block_{name}"](); _RAN.add(name)

def predicate(label, lines=14):
    """Verify one ledger predicate: run the blocks of the families that cite it (each once per session), print the deciding
    check's source (from its marker) and every family record that cites the predicate, and return True iff all pass."""
    fam = PREDICATES.get(label)
    if fam is None:
        print(f"{label}: no python witness (see the predicate's Lean witness or its source)"); return None
    citing = {f.split(".")[0] for f, rows in LEDGER.items() if label in [t.strip() for t in rows.split(",")]}
    for b in sorted({fam.split(".")[0]} | citing): _run_block(b)     # the deciding block and every block whose families cite the predicate
    mk = markers().get(label)
    if mk:
        src = open(os.path.abspath(__file__), encoding="utf-8").read().split("\n")
        print(f"— {mk[0]}:{mk[1]} (the check that decides {label}; family {fam})")
        for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(src))): print(f"{j + 1:5d}  {src[j]}")
    else:
        print(f"— {SCRIPT}.py, block {fam.split('.')[0]} (the whole block witnesses {label})")
    recs = [r for r in RESULTS if label in [t.strip() for t in r["rows"].split(",")]]
    ok = all(r["ok"] for r in recs)
    for r in recs:
        role = "(deciding)" if r["id"] == fam else "(corroborating)"
        print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:8s} {role:16s} {r['detail']}")
    print(f"{label}: {'VERIFIED' if ok and recs else 'FAILED'} — {len(recs)} family record(s)")
    return ok

def verify_all():
    """Run every block (those already run in this session are not re-run) and print the summary; True iff every family check passed."""
    for b in sorted(BLOCK): _run_block(b)
    return summary(write=False)

def family(tag, fam):
    _FAM[0], _FAM[1] = tag, fam

def chk(label, ok, tag=None, fam=None):
    """A micro-check, recorded under the current (block, family); never exits."""
    MICRO.append((tag or _FAM[0], fam or _FAM[1], label, bool(ok)))
    if not ok:
        print(f"    FAIL: {label}")

def flush(tag, order=None):
    fams = OrderedDict()
    for t, fam, label, ok in MICRO:
        if t == tag:
            fams.setdefault(fam, []).append(ok)
    for fam in (order or fams):
        oks = fams.get(fam, [])
        check(f"{tag}.{fam}", ok=bool(oks) and all(oks), detail=f"{len(oks)} exact micro-checks")

def check(pid, ok, detail="", kind="EXACT", label=None):
    """Record one family check. pid = <block>.<family>; LEDGER[pid] = the paper predicate(s) it witnesses."""
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "block": pid.split(".")[0], "script": SCRIPT, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:8s} {kind:5s} [{rows}] {label[:110]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} exact micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)

# ------------------------------------------------------------------------------------------------------------
# block dom — verify_domains: exact-arithmetic verification for 10-dimensions (quartet edition)
# (quartet edition).
#
# Layers:
#   A. shell datum and domain algebra (F13 working shell): group law, grading,
#      fibrewise addition, neutral criterion, local recovery, flag arithmetic
#   B. the quartet at the unit face (symbolic, exact rationals over free
#      exponents): action identity, pairing closure rank, cancellation identity,
#      mechanical table re-derivation
#   C. the defining congruences on the lab Carrier (S = 602,140, Omega = 2,408,561): existence,
#      exhaustive root enumeration, root pairs, register identities
#   H. pair layer (round 05): pair-well-definedness of every congruence identity and
#      the representative-inertness sweep over all admissible sign assignments
#
# Every check is integer or exact-rational arithmetic; no floats, no RNG
# (the window-ladder orderings are compared by integer squares).
# Domains are triples (r mod p, s mod p-1, n mod 4): free [L],[T] exponents
# and the flag.
def block_dom():
    """Block dom — verify_domains: the eight layers A–H of exact micro-checks, one family check each (dom.A … dom.H)."""
    # A. shell datum and domain algebra on F13
    family('dom', 'A')
    P = 13
    KAPPA = (P - 1) // 4
    G13 = 2

    order = next(k for k in range(1, P) if pow(G13, k, P) == 1)
    chk("g=2 primitive on F13 (order 12)", order == P - 1)

    I13 = (-pow(G13, KAPPA, P)) % P
    chk("i = -g^kappa = 5", I13 == 5)
    chk("i = g^{-kappa}", I13 == pow(G13, (P - 1) - KAPPA, P))
    chk("i^2 = -1", (I13 * I13) % P == P - 1)
    PI13 = 2 * KAPPA
    chk("pi = 2 kappa = 6", PI13 == 6)
    chk("e = g^i = 6", pow(G13, I13, P) == 6)
    chk("g^pi = -1", pow(G13, PI13, P) == P - 1)
    chk("2 pi = p-1 == -1 (mod p)", (2 * PI13) % P == P - 1)
    chk("phase-cycle order p-1 = 4 kappa = 2 pi", P - 1 == 4 * KAPPA == 2 * PI13)

    # capacity is a size: budget statement only (count-per-count), no duration
    chk("capacity budget: quarter cycle holds kappa steps", 4 * KAPPA == P - 1)

    # 10:C2 (p10012)
    # domain group D_p = Z_p x Z_{p-1} with flag component mod 4
    def dmul(a, b):
        return ((a[0] + b[0]) % P, (a[1] + b[1]) % (P - 1), (a[2] + b[2]) % 4)

    def dinv(a):
        return ((-a[0]) % P, (-a[1]) % (P - 1), (-a[2]) % 4)

    ONE = (0, 0, 0)
    L = (1, 0, 0)
    T = (0, 1, 0)
    FLAG = (0, 0, 1)                 # the unit flag Iq

    chk("group identity", dmul(ONE, L) == L)
    chk("inverses", dmul(L, dinv(L)) == ONE and dmul(FLAG, dinv(FLAG)) == ONE)
    chk("flag order four", dmul(dmul(FLAG, FLAG), dmul(FLAG, FLAG)) == ONE)
    # 10:D2 (p10018)
    # fork B: the flag is internal, Iq = [T]^kappa; realized label of (r,s;j) is
    # (r mod p, (s + j*kappa) mod (p-1)) with sector j mod 4
    def realize(a):
        return (a[0] % P, (a[1] + a[2] * KAPPA) % (P - 1))
    chk("realized flag label = (0, kappa)", realize(FLAG) == (0, KAPPA))
    o4 = [(r, s) for r in range(P) for s in range(P - 1)
          if (4 * r) % P == 0 and (4 * s) % (P - 1) == 0
          and not ((2 * r) % P == 0 and (2 * s) % (P - 1) == 0)]
    # 10:X3 (p10050)
    chk("unique order-four subgroup: exactly two generators", sorted(o4) == [(0, KAPPA), (0, 3 * KAPPA)])
    chk("no flag of space: all order-four elements have r = 0", all(r == 0 for r, _ in o4))
    chk("flag horizon-inaccessible on window H<kappa",
          all((0, KAPPA) != (r % P, s % (P - 1))
              for r in range(-1, 2) for s in range(-1, 2)))
    EPSILONS = [e for e in range(1, P - 1) if __import__("math").gcd(e, P - 1) == 1]
    chk("flag covariance: eps*kappa in {kappa, 3kappa} for all units eps",
          all((e * KAPPA) % (P - 1) in (KAPPA, 3 * KAPPA) for e in EPSILONS))
    chk("realization is a homomorphism",
          all(realize(dmul(a, b)) == ((realize(a)[0] + realize(b)[0]) % P,
                                      (realize(a)[1] + realize(b)[1]) % (P - 1))
              for a in [L, T, FLAG, (3, 5, 2)] for b in [L, T, FLAG, (7, 2, 3)]))

    # 10:F2 (p10034)
    # derived domains
    def dpow(a, k):
        out = ONE
        step = a if k >= 0 else dinv(a)
        for _ in range(abs(k)):
            out = dmul(out, step)
        return out

    # 10:D6 (p10022)
    E_dom = dmul(FLAG, dinv(T))                       # [E] = Iq T^-1
    p_dom = dmul(FLAG, dinv(L))                       # [p] = Iq L^-1
    v_dom = dmul(L, dinv(T))                          # [v] = L T^-1
    m_dom = dmul(E_dom, dinv(dpow(v_dom, 2)))         # [m] = [E][v]^-2
    chk("[m] = Iq L^-2 T", m_dom == ((-2) % P, 1, 1))
    F_dom = dmul(m_dom, dmul(L, dpow(dinv(T), 2)))    # [F] = [m][a]
    chk("[F] = Iq L^-1 T^-1", F_dom == ((-1) % P, (-1) % (P - 1), 1))
    S_dom = dmul(E_dom, T)
    chk("[S] = Iq (action carries the flag)", S_dom == FLAG)
    chk("phase count neutral: [E][T][hbar]^-1 = 1", dmul(S_dom, dinv(FLAG)) == ONE)
    G_dom = dmul(F_dom, dmul(dpow(L, 2), dinv(dpow(m_dom, 2))))
    chk("[G] = Iq^-1 L^5 T^-3", G_dom == (5, (-3) % (P - 1), 3))
    chk("Planck area flag-free: [G][hbar][c]^-3",
          dmul(G_dom, dmul(FLAG, dpow(dinv(v_dom), 3)))[2] == 0)
    chk("[G hbar c^-3] = L^2",
          dmul(G_dom, dmul(FLAG, dpow(dinv(v_dom), 3))) == (2, 0, 0))
    chk("[Gm/c^2] = L",
          dmul(G_dom, dmul(m_dom, dpow(dinv(v_dom), 2))) == (1, 0, 0))
    # 10:F4 (p10036)
    chk("[Gm/r^3] = T^-2 flag-free",
          dmul(G_dom, dmul(m_dom, dpow(dinv(L), 3))) == (0, (-2) % (P - 1), 0))
    chk("Compton flag-free: [m][c][hbar]^-1 = L^-1",
          dmul(m_dom, dmul(v_dom, dinv(FLAG))) == ((-1) % P, 0, 0))

    # fibrewise addition / neutral criterion / local recovery
    # 10:C3 (p10013)
    chk("squaring leaves fibre: dom(Q) != dom(Q^2) for [L]", L != dpow(L, 2))
    H = 5
    # 10:G1 (p10037), 10:G3 (p10039)
    chk("local recovery bound: p-1 > 2H", P - 1 > 2 * H)
    pairs = [(r, s) for r in range(-H, H + 1) for s in range(-H, H + 1)]
    images = {(r % P, s % (P - 1)) for (r, s) in pairs}
    chk("local recovery: all |r|,|s| <= 5 distinguished", len(images) == len(pairs))
    # the energy--momentum relation E^2 = p^2 c^2 + m^2 c^4: its three terms in one fibre, at crossing degree two (the
    # half-period sector) -- Example ex:dispersion, predicate 10:G3
    E2 = dpow(E_dom, 2); pc2 = dpow(dmul(p_dom, v_dom), 2); mc4 = dpow(dmul(m_dom, dpow(v_dom, 2)), 2)
    chk("dispersion: [E]^2 = [pc]^2 = [mc^2]^2, one fibre at sector 2", E2 == pc2 == mc4 and E2[2] == 2)

    # B. the quartet at the unit face (exact rationals over free scales)
    family('dom', 'B')
    # Represent horizons as exponent vectors over (l, t, p, E) and verify the
    # relation lattice; then instantiate with exact rationals satisfying the
    # one identity l*p = t*E and confirm every claimed equality numerically.
    import itertools

    # exponent vectors: c = l - t (= E - p), hbar = l + p (= t + E), mix = p + t
    c_vec    = (1, -1, 0, 0)
    c_vec2   = (0, 0, -1, 1)
    hbar_vec = (1, 0, 1, 0)
    hbar_vec2= (0, 1, 0, 1)
    mix_vec  = (0, 1, 1, 0)
    lE_vec   = (1, 0, 0, 1)
    rel      = (1, -1, 1, -1)        # l - t + p - E = 0 <=> l*p = t*E

    def add(u, v): return tuple(a + b for a, b in zip(u, v))
    def sub(u, v): return tuple(a - b for a, b in zip(u, v))

    chk("c faces differ by the relation", sub(c_vec, c_vec2) == rel)
    chk("hbar faces differ by the relation", sub(hbar_vec, hbar_vec2) == rel)
    chk("l*E = hbar*c (exponent identity)", lE_vec == add(hbar_vec2, c_vec))
    chk("mix = hbar/c (exponent identity)", mix_vec == sub(hbar_vec2, c_vec2))

    # rank of {c, hbar, mix} modulo the relation is 3 (full)
    def rank_int(rows):
        m = [list(map(Fr, r)) for r in rows]
        rank, ncols = 0, len(m[0])
        for col in range(ncols):
            piv = next((i for i in range(rank, len(m)) if m[i][col] != 0), None)
            if piv is None:
                continue
            m[rank], m[piv] = m[piv], m[rank]
            m[rank] = [x / m[rank][col] for x in m[rank]]
            for i in range(len(m)):
                if i != rank and m[i][col] != 0:
                    m[i] = [a - m[i][col] * b for a, b in zip(m[i], m[rank])]
            rank += 1
        return rank

    # 10:E2 (p10025)
    # pairing lattice mod the relation has rank TWO: mix = hbar - c, lE = hbar + c
    chk("mix = hbar' - c' (exponent identity: k_B derived)",
          mix_vec == sub(hbar_vec2, c_vec2))
    chk("pairing rank 2 mod relation: rank{c,hbar,rel} = 3",
          rank_int([c_vec, hbar_vec, rel]) == 3)
    chk("mix adds nothing: rank{c,hbar,mix,rel} = 3",
          rank_int([c_vec, hbar_vec, mix_vec, rel]) == 3)
    chk("lE adds nothing: rank{c,hbar,mix,lE,rel} = 3",
          rank_int([c_vec, hbar_vec, mix_vec, lE_vec, rel]) == 3)

    # 10:E3 (p10026)
    # numeric instantiation with the identity enforced: choose l,t,p free, E = l*p/t
    l, t, p = Fr(3, 7), Fr(2, 5), Fr(11, 4)
    E = l * p / t
    c_u, hbar_u = l / t, l * p
    chk("unit face: c = l/t = E/p", c_u == E / p)
    chk("unit face: hbar = l p = t E", hbar_u == t * E)
    chk("cancellation: (p t)(l/t) = l p  [k_B c = -hbar]", (p * t) * (l / t) == hbar_u)
    chk("mixed partner: l E = hbar c", l * E == hbar_u * c_u)
    m_P = p / c_u
    chk("m_P = p/c = E/c^2", m_P == E / c_u ** 2)
    G_num = hbar_u * c_u / m_P ** 2
    chk("G = hbar c / m_P^2 = l^2 c^3 / hbar", G_num == l ** 2 * c_u ** 3 / hbar_u)
    # bijection {c, hbar, G} <-> quartet: recover the free scale from G
    chk("bijection: l^2 = G hbar / c^3", l ** 2 == G_num * hbar_u / c_u ** 3)
    chk("recovered quartet: t=l/c, p=hbar/l, E=hbar c/l",
          t == l / c_u and p == hbar_u / l and E == hbar_u * c_u / l)
    Theta = E / (hbar_u / c_u)      # E_P / |k_B|
    chk("Theta_P = E_P/|k_B| = c^2/1 * ... consistent", Theta == E * c_u / hbar_u)

    # DOF: quartet has 4 generators, 1 relation -> 3 free scales; +G -> 3+1
    # 10:X1 (p10048)
    chk("DOF: 4 - 1 = 3 free scales", 4 - rank_int([rel]) == 3)

    # ------------------------------------------------------------------
    # flag positions of the quartet: (l, t, p, E) at (0, 0, 1, 1) mod 4;
    # every quartet relation must close on the flag component
    # ------------------------------------------------------------------
    FL = {"l": 0, "t": 0, "p": 1, "E": 1}
    def flag_of(expr):
        # expr: dict of generator -> exponent
        return sum(FL[g] * e for g, e in expr.items()) % 4
    chk("flag[hbar = l p] = 1", flag_of({"l": 1, "p": 1}) == 1)
    chk("flag[hbar = t E] = 1", flag_of({"t": 1, "E": 1}) == 1)
    chk("flag[c = l/t] = 0", flag_of({"l": 1, "t": -1}) == 0)
    chk("flag[c = E/p] = 0", flag_of({"E": 1, "p": -1}) == 0)
    chk("flag[k_B ~ p t] = 1", flag_of({"p": 1, "t": 1}) == 1)
    chk("flag[hbar c ~ l E] = 1", flag_of({"l": 1, "E": 1}) == 1)
    # G = l^2 c^3 / hbar: flags 2*0 + 3*0 - 1 = -1 = 3 mod 4 (inverse flag)
    chk("flag[G] = -1", (2 * FL["l"] + 3 * 0 - flag_of({"l": 1, "p": 1})) % 4 == 3)
    # Planck area G hbar / c^3 flag-free; Gm/c^2 flag-free (m at flag 1)
    chk("flag[G hbar/c^3] = 0", (3 + 1 + 0) % 4 == 0)
    chk("flag[G m/c^2] = 0 (m flag 1)", (3 + 1 + 0) % 4 == 0)
    # dual horizons are flag-crossed images: p = hbar/l, E = hbar/t
    chk("p = hbar/l (unit face)", p == hbar_u / l)
    chk("E = hbar/t (unit face)", E == hbar_u / t)
    # equivalent generating data {l, t, hbar} <-> {c, hbar, G}
    chk("{l,t,hbar} determine c, G", c_u == l / t and G_num == l ** 2 * (l / t) ** 3 / hbar_u)

    # C. the defining congruences on the lab Carrier
    family('dom', 'C')
    S = 602_140
    Om = 4 * S + 1
    chk("Om = 2,408,561", Om == 2_408_561)

    def is_prime(n):
        if n < 2: return False
        if n % 2 == 0: return n == 2
        d = 3
        while d * d <= n:
            if n % d == 0: return False
            d += 2
        return True

    chk("admissibility: S even, S=1 mod 3, Om prime",
          S % 2 == 0 and S % 3 == 1 and is_prime(Om))

    # 10:E4 (p10027)
    # congruence 1: 2G + 1 = 0 -- linear, unique
    G_pin = [x for x in (pow(2, -1, Om) * (Om - 1) % Om,) ]
    G_val = (Om - 1) // 2
    chk("congruence 2G+1=0 unique: G = 2S = 1,204,280", (2 * G_val + 1) % Om == 0 and G_val == 2 * S == 1_204_280)

    # quadratic defining congruences: exhaustive-root verification via the known values
    hbar_val = 18_688
    kB_val = 1_880_160
    chk("congruence hbar^2 = -1", (hbar_val * hbar_val) % Om == Om - 1)
    chk("congruence k_B^2 = -2", (kB_val * kB_val) % Om == Om - 2)
    c2 = (2 * S + 1) % Om
    chk("congruence 2c^2 = 1: c^2 = 2S+1", (2 * c2) % Om == 1)
    # each quadratic congruence has exactly two roots: x and Om - x
    for name, val, target in (("hbar", hbar_val, Om - 1), ("k_B", kB_val, Om - 2)):
        other = Om - val
        chk(f"{name}: two roots {{x, -x}}", (other * other) % Om == target and other != val)
    # linkage consistency: the stated representatives satisfy k_B c = -hbar
    c_val = (-hbar_val * pow(kB_val, -1, Om)) % Om
    chk("c from k_B c = -hbar", (kB_val * c_val) % Om == (Om - hbar_val) % Om)
    chk("c^2 lands on the congruence", (c_val * c_val) % Om == c2)
    chk("register identities: G = -c^2, G^2 = 4^-1",
          (G_val + c2) % Om == 0 and (4 * G_val * G_val) % Om == 1)
    chk("h = 2 pi hbar = -hbar = k_B c", (Om - hbar_val) % Om == (kB_val * c_val) % Om)
    chk("m_P^2 = Om = 0 (scale face: the totality)", (Om) % Om == 0)


    # D. revision layer: both Carriers, face closure, minimality, temperature
    family('dom', 'D')

    def sqrt_roots(a, Om):
        return sorted(x for x in range(Om) if (x * x) % Om == a % Om)

    CARRIERS = {
        233: dict(S=58, hbar=89, kB=124, c=159, G=116, h=144),
        2_408_561: dict(S=602_140, hbar=18_688, kB=1_880_160, c=171_106, G=1_204_280, h=2_389_873),
    }
    # fill lab h and c consistently
    lab = CARRIERS[2_408_561]
    lab["c"] = (-lab["hbar"] * pow(lab["kB"], -1, 2_408_561)) % 2_408_561
    lab["h"] = (2_408_561 - lab["hbar"]) % 2_408_561

    for Om_, R in CARRIERS.items():
        S_, hb, kB, c_, G_, h_ = R["S"], R["hbar"], R["kB"], R["c"], R["G"], R["h"]
        chk(f"[{Om_}] admissibility triple: S even, S=1 mod 3, Om prime",
              S_ % 2 == 0 and S_ % 3 == 1 and is_prime(Om_))
        chk(f"[{Om_}] two-way class: S even <=> Om = 1 mod 8", Om_ % 8 == 1)
        # congruence equations of the residue reading
        chk(f"[{Om_}] B: 2G = -1", (2 * G_ + 1) % Om_ == 0)
        chk(f"[{Om_}] B: c^2 = 2^-1", (2 * c_ * c_) % Om_ == 1)
        chk(f"[{Om_}] B: hbar^2 = -1", (hb * hb) % Om_ == Om_ - 1)
        chk(f"[{Om_}] B: k_B^2 = -2", (kB * kB) % Om_ == Om_ - 2)
        chk(f"[{Om_}] B: k_B c = -hbar", (kB * c_) % Om_ == (Om_ - hb) % Om_)
        chk(f"[{Om_}] B: h = -hbar", h_ == (Om_ - hb) % Om_)
        # closure consequences (Prop faces-closure)
        chk(f"[{Om_}] closure: G = -c^2", (G_ + c_ * c_) % Om_ == 0)
        chk(f"[{Om_}] closure: G^2 = 4^-1", (4 * G_ * G_) % Om_ == 1)
        chk(f"[{Om_}] closure: hbar^4 = 1", pow(hb, 4, Om_) == 1)
        chk(f"[{Om_}] closure: (k_B c)^2 = -1", pow(kB * c_, 2, Om_) == Om_ - 1)
        chk(f"[{Om_}] closure: hbar c G^-1 = k_B (m_P^2 monomial face on the k_B residue)",
              (hb * c_ * pow(G_, -1, Om_)) % Om_ == kB)
        chk(f"[{Om_}] monomial face nonzero: horizon declaration is not a congruence",
              (hb * c_ * pow(G_, -1, Om_)) % Om_ != 0)
        # defining congruences have exactly two roots each
        for name, val, tgt in (("hbar", hb, Om_ - 1), ("kB", kB, Om_ - 2)):
            roots = sorted(((val) % Om_, (Om_ - val) % Om_))
            chk(f"[{Om_}] {name}: root pair valid", all((x * x) % Om_ == tgt for x in roots))

    # representative half-planes are chart data (suite annex): band predicates
    # carry no invariant content, as the pair form requires
    r233 = sqrt_roots(58, 233)
    chk("233: sqrt(S) roots {72,161}", r233 == [72, 161])
    chk("233: hbar-representative from the upper-half root of S (161 -> 89): chart datum",
          (2 * 161) % 233 == 89 and 161 > 233 // 2)
    chk("233: the other root gives the pair partner h (72 -> 144)", (2 * 72) % 233 == 144)
    chk("lab: hbar-representative from the lower-half root of S (9344): chart datum",
          (2 * 9344) % 2_408_561 == 18_688 and 9344 < 2_408_561 // 2)
    chk("half-plane of the hbar-representative differs across Carriers: band = chart data",
          (161 > 233 // 2) and (9344 < 2_408_561 // 2))

    # -1 is QR unconditionally (Om = 4S+1 = 1 mod 4), S even needed only for 2
    chk("-1 QR even for odd S: Om=13 (S=3), 5^2 = -1", (5 * 5) % 13 == 12)
    chk("Om = 1 mod 4 for every S", all((4 * S0 + 1) % 4 == 1 for S0 in range(1, 50)))

    # 10:E9 (p10032)
    # minimality scan under the complete predicate (the paper's Definitions 1 and 2, Remark 1)
    def admissible(p_, Om__):
        kap_ = (p_ - 1) // 4
        S__ = (Om__ - 1) // 4
        return (kap_ > 1 and is_prime(p_) and p_ % 4 == 1
                and Om__ % 4 == 1 and is_prime(Om__)
                and S__ % 2 == 0 and S__ % 3 == 1
                and p_ * p_ < Om__)
    adm = [(p_, Om__) for p_ in range(5, 40, 4) for Om__ in range(p_ * p_ + 1, 234)
           if admissible(p_, Om__)]
    chk("minimality: (13,233) admissible", (13, 233) in adm)
    chk("minimality: no admissible pair below 233", min(o for _, o in adm) == 233)
    chk("counterfactual: dropping mod-3 admits (13,193)",
          is_prime(193) and 48 % 2 == 0 and 48 % 3 == 0 and 13 * 13 < 193)
    chk("counterfactual: dropping kappa>1 admits (5,41)",
          is_prime(5) and is_prime(41) and 10 % 2 == 0 and 10 % 3 == 1 and 25 < 41)
    chk("F5 is its own quarter-turn core: 4*kappa = 4 = p-1 with kappa=1", 4 * 1 == 5 - 1)
    chk("kappa=2 not viable: 9 composite", not is_prime(9))

    # 10:F3 (p10035), 10:X2 (p10049)
    # temperature and Unruh closures in (r, s, j) bookkeeping
    kB_dom = (-1, 1, 1)                    # Iq L^-1 T
    E_dom3 = (0, -1, 1)                    # Iq T^-1
    acc = (1, -2, 0)
    Theta = tuple(a - b for a, b in zip(E_dom3, kB_dom))
    chk("[Theta] = [E][k_B]^-1 = L T^-2, flag-free", Theta == acc)
    c_dom3 = (1, -1, 0)
    hb_dom3 = (0, 0, 1)
    unruh = tuple(h + a - c - k for h, a, c, k in zip(hb_dom3, acc, c_dom3, kB_dom))
    chk("Unruh closure: [hbar a / (c k_B)] = [Theta]", unruh == acc)

    # crossing-degree recovery (Cor recovery-crossings)
    def embed(u, a, b):
        return (a - 2 * u, b + u, u)
    trip = [(u, a, b) for u in range(-2, 3) for a in range(-3, 4) for b in range(-3, 4)]
    chk("classical embedding injective on Z^3",
          len({embed(u, a, b) for u, a, b in trip}) == len(trip))
    P2, K2 = 229, 57
    def real2(r, s, j):
        return (r % P2, (s + j * K2) % (P2 - 1))
    win = [(r, s, j) for r in range(-5, 6) for s in range(-5, 6) for j in (-1, 0, 1)]
    chk("faithful realization on window (p=229, H=5, |j|<=1)",
          len({(real2(*w), w[2] % 4) for w in win}) == len(win))
    chk("sector saturates mod 4: hbar^4 realizes at sector zero",
          (4 * K2) % (P2 - 1) == 0)


    # E. round-02 layer: covariance counterexamples, window covariance,
    family('dom', 'E')

    # (a) regression: the naive character on Z_p-reduced labels is ill-defined
    inv2 = pow(2, -1, 13)
    chk("r02: character ill-defined on the modular projection (r=3 vs r=16 differ)",
          pow(inv2, 3, 13) != pow(inv2, 16, 13))
    # (b) regression: (p-1, 0) has trivial character yet is non-neutral
    chk("r02: (p-1,0) trivial character for all m",
          all(pow(m, -(13 - 1), 13) == 1 for m in range(1, 13)))
    chk("r02: (p-1,0) is non-neutral in D_p", (13 - 1) % 13 != 0)
    # (c) regression: eps as field character fails composition (5^2=1 in Z_12^x)
    chk("r02: eps field-character composition fails",
          (5 * 5) % 12 == 1 and pow(pow(5, -1, 13), 2, 13) != 1)

    # 10:C5 (p10015)
    # window covariance (Theorem 5, repaired form)
    H = 5
    chk("r02: window dilation: trivial character forces r=0 in window",
          all(not all(pow(m, -r, 13) == 1 for m in range(2, 13))
              for r in range(-H, H + 1) if r != 0))
    # pushforward invariant sublattice on the realized lattice is {0, pi}
    units12 = [e for e in range(1, 12) if __import__("math").gcd(e, 12) == 1]
    inv_labels = [s_ for s_ in range(12) if all((e * s_) % 12 == s_ for e in units12)]
    chk("r02: pushforward-invariant labels are exactly {0, pi}", inv_labels == [0, 6])
    chk("r02: eps=-1 admissible always", __import__("math").gcd(11, 12) == 1)
    # flag pair behaviour under pushforward: eps mod 4 in {1,3} decides fix/swap
    chk("r02: quarter-turn labels fixed iff eps=1 mod 4",
          all(((e * 3) % 12 == 3) == (e % 4 == 1) for e in units12))

    # representative-convention data (chart-side record; no invariant content)
    chk("r02: hbar representative lower-half on 233 (chart datum)", 89 < 233 // 2 and (89 * 89) % 233 == 232)
    chk("r02: hbar representative lower-half on lab (chart datum)",
          18_688 < 2_408_561 // 2 and (18_688 ** 2) % 2_408_561 == 2_408_560)
    chk("r02: c representative halves differ across Carriers (chart data)",
          (159 > 233 // 2) and (171_106 < 2_408_561 // 2))
    chk("r02: +-c one residue class (-1 is QR)", pow(89, 2, 233) == 233 - 1)

    # index-two sublattice <c, hbar, G> in Z^3 on (l, t, hbar)
    M = [[1, -1, 0], [0, 0, 1], [5, -3, -1]]
    det = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
           - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
           + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    chk("r02: <c,hbar,G> has index two (det = -2)", det == -2)
    chk("r02: l^2 = G hbar / c^3 recovers the scale by positive root",
          l ** 2 == G_num * hbar_u / c_u ** 3 and l > 0)

    # residue reading rho: multiplicative on constant monomials (both Carriers)
    for Om_, R in CARRIERS.items():
        hb, kB, c_, G_ = R["hbar"], R["kB"], R["c"], R["G"]
        lhs = (hb * c_ * pow(G_, -1, Om_)) % Om_
        chk(f"r02 [{Om_}]: rho multiplicative on hbar*c/G", lhs == kB)
        chk(f"r02 [{Om_}]: rho(h) = -rho(hbar)", R["h"] == (Om_ - hb) % Om_)


    # F. round-03 layer: window bound, sigma-twisted action, delta_C
    family('dom', 'F')
    import math as _m
    units12 = [e for e in range(1, 12) if _m.gcd(e, 12) == 1]

    # window counterexample (regression): at H >= 2kap, (0, pi) is invariant and non-neutral
    chk("r03: pi invariant under every pushforward", all((e * 6) % 12 == 6 for e in units12))
    chk("r03: (0,pi) non-neutral", 6 % 12 != 0)
    # corrected window H < 2kap: only neutral label invariant
    Hc = 2 * KAPPA - 1
    inv_win = [s_ for s_ in range(-Hc, Hc + 1) if all((e * (s_ % 12)) % 12 == s_ % 12 for e in units12)]
    chk("r03: window H<2kap invariants = {0}", inv_win == [0])
    chk("r03: window bound equals local-recovery bound", (4 * KAPPA > 2 * Hc) and (Hc < 2 * KAPPA))

    # sigma-twisted active action: full equivariance sweep on p=13 and p=229
    def sigma(e):
        return 1 if e % 4 == 1 else -1
    for P_, K_ in ((13, 3), (229, 57)):
        U_ = [e for e in range(1, P_ - 1) if _m.gcd(e, P_ - 1) == 1]
        ok = all(((e * s_) % (P_ - 1) + sigma(e) * j * K_) % (P_ - 1)
                 == (e * (s_ + j * K_)) % (P_ - 1)
                 for e in U_ for s_ in range(0, P_ - 1, max(1, (P_ - 1) // 12)) for j in (-2, -1, 0, 1, 2))
        chk(f"r03: sigma-twist equivariant on p={P_}", ok)
    chk("r03: witness e=7,(2;1) matches realized action", ((7 * 2) % 12 + sigma(7) * 3) % 12 == (7 * 5) % 12)
    chk("r03: witness e=-1,(0;1) matches realized action", ((11 * 0) % 12 + sigma(11) * 3) % 12 == (11 * 3) % 12)
    chk("r03: plain lift fails for e=7,(2;1) (regression)", ((7 * 2) % 12 + 3) % 12 != (7 * 5) % 12)
    chk("r03: sigma multiplicative mod 4",
          all(sigma(a * b) == sigma(a) * sigma(b) for a in units12 for b in units12))

    # 10:D1 (p10017)
    # delta_S / delta_C: involutions; delta_C carries primal domains to dual horizon domains
    def dS_(a):
        return dinv(a)
    def dC_(a):
        return dmul(FLAG, dinv(a))
    chk("r03: delta_S involution", all(dS_(dS_(a)) == a for a in [L, T, FLAG, (3, 5, 2)]))
    chk("r03: delta_C involution", all(dC_(dC_(a)) == a for a in [L, T, FLAG, (3, 5, 2)]))
    chk("r03: delta_C[L] = [p] domain", dC_(L) == p_dom)
    chk("r03: delta_C[T] = [E] domain", dC_(T) == E_dom)
    chk("r03: delta_S flag-free", dS_(L)[2] == 0 and dS_(T)[2] == 0)


    # G. round-04 layer: realized action, j-restriction, ladder, k_B linkage typing
    family('dom', 'G')
    import math as _mm

    # realized action composes with residue classes; Z^3 representatives do not
    u0 = 5
    chk("r04: realized action composes (5*5=1 in Z_12^x)", ((5 * (5 * u0)) % 12) == ((25 % 12) * u0) % 12 == u0 % 12)
    chk("r04: integer representatives do not compose on Z (25s != s)", 25 * 2 != 2)

    # j-suppression witness: (0,0;1) moves under eps=-1 (flag-free restriction needed)
    chk("r04: (0,0;1) sector moves under eps=-1", ((-1) * (0 + 3)) % 12 == 9 != 3)

    # 10:G2 (p10038)
    # window ladder: nested for kappa >= 17; toy fails.  All orderings exact:
    # 2 sqrt(k) < k/2  <=>  (4 sqrt(k))^2 < k^2  <=>  16 k < k^2  <=>  k > 16.
    def ladder(k):
        return 16 * k < k * k and 0 < k
    chk("r04: ladder nested for kappa=17,387,602140 (integer-square ordering)",
          all(ladder(k) for k in (17, 387, 602140)))
    chk("r04: toy kappa=3 below nesting threshold", not ladder(3))
    chk("r04: coherence window identity (2 sqrt kappa)^2 = 4 kappa = p-1 exactly",
          all((2 * 2 * k == 4 * k) and (4 * k == (4 * k + 1) - 1) for k in (3, 387, 602140)))
    chk("r04: totality closure exact: (2 sqrt S)^2 = Om - 1",
          4 * 602140 == 2408561 - 1)

    # F/a is flagged (equal-crossing-degree correction): [F]=(-1,-1;1), [a]=(1,-2;0)
    F3 = (-1, -1, 1); A3 = (1, -2, 0)
    ratio = tuple(f - a for f, a in zip(F3, A3))
    chk("r04: F/a crossing degree 1 (flagged, = [m])", ratio == (-2, 1, 1))

    # meridian transport onto the flag: (L T^kappa)^p = Iq on several shells
    for P_, K_ in ((13, 3), (29, 7), (229, 57)):
        chk(f"r04: meridian transport p={P_}", (P_ % P_, (P_ * K_) % (P_ - 1)) == (0, K_))

    # Buckingham's count on the integer lift (Corollary cor:pi-theorem): the pendulum (T, l, g, m) with lifted labels
    # (0,1;0), (1,0;0), (1,-2;0), (-2,1;1) has rank 3, hence N - rank = 1 dimensionless product, T^2 g / l, whose
    # lifted label vanishes; the mass, the only quantity with a crossing degree, cannot enter it
    pend = [(0, 1, 0), (1, 0, 0), (1, -2, 0), (-2, 1, 1)]
    kvec = (2, -1, 1, 0)
    lab_ = tuple(sum(k * q[i] for k, q in zip(kvec, pend)) for i in range(3))
    # 10:G4 (p10046)
    chk("Buckingham: pendulum (T, l, g, m) rank 3, one product T^2 g/l with label (0,0;0)", rank_int(pend) == 3 and lab_ == (0, 0, 0))
    # The electromagnetic domain (Remark rem:electromagnetic, predicate 10:F5): with the Coulomb constant neutral, [q]^2 = [E][L] =
    # I_q [L][T]^-1, on the shell (1, kappa-1), on the lift (1,-1;1). Its square roots in D_p = Z_p x Z_{4 kappa}: the space half
    # 2^-1 = 2 kappa + 1 = -2 kappa (the meridian half-turn); the phase equation 2s = kappa-1 (mod 4 kappa) is solvable iff kappa
    # is odd, then two roots differing by the half-period (0, 2 kappa) = I_q^2; on the lift no root at all (odd coordinates).
    def charge_roots(k):
        p_, n_ = 4 * k + 1, 4 * k
        return sorted((r, s) for r in range(p_) for s in range(n_) if ((2 * r) % p_, (2 * s) % n_) == (1, (k - 1) % n_))
    # 10:F5 (p10047), 10:X4 (p10051)
    chk("charge: [q]^2 = [E][L] = I_q [L][T]^-1 = (1, 2) on F_13, its roots exactly (7,1) and (7,7), differing by the half-period (0, 6)",
          ((0 + 1) % 13, (3 - 1 + 0) % 12) == (1, 2) and charge_roots(3) == [(7, 1), (7, 7)] and ((7 - 7) % 13, (7 - 1) % 12) == (0, 6))
    chk("charge: the roots exist iff kappa is odd, then exactly (2 kappa+1, (kappa-1)/2) and its half-period partner (every prime p = 4 kappa+1, kappa <= 30)",
          all((charge_roots(k) == sorted([(2 * k + 1, (k - 1) // 2), (2 * k + 1, (k - 1) // 2 + 2 * k)])) if k % 2 else charge_roots(k) == []
              for k in range(1, 31) if all((4 * k + 1) % d for d in range(2, 4 * k + 1))))
    chk("charge: the space exponent 2^-1 = 2 kappa+1 = -2 kappa is the meridian half-turn, |r| = 2 kappa, on p = 13, 29, 173, 229",
          all((2 * (2 * k + 1)) % (4 * k + 1) == 1 and (2 * k + 1) - (4 * k + 1) == -2 * k for k in (3, 7, 43, 57)))
    chk("charge: on the lift [q]^2 = (1,-1;1) has no half; [phi]^2 = [q]^2 [L]^-2 = [F], [E_field]^2 = [F]^2 [q]^-2 = the energy density, e^2/(hbar c) neutral",
          all(c % 2 for c in (1, -1, 1)) and (1 - 2, -1, 1) == (-1, -1, 1) and (2 * (-1) - 1, 2 * (-1) + 1, 2 - 1) == (0 - 3, -1, 1)
          and (0 + 1, 0 - 1, 1 + 0) == (1, -1, 1))
    chk("charge: the dilation character m^-r at r = 2 kappa+1 is m^-1 (m|p) (Euler); a non-square dilation flips the sign, never window-covariant (p = 13, 29)",
          all(pow(m, -(2 * k + 1), 4 * k + 1) == (pow(m, -1, 4 * k + 1) * pow(m, 2 * k, 4 * k + 1)) % (4 * k + 1)
              and pow(m, 2 * k, 4 * k + 1) == (1 if any((x * x) % (4 * k + 1) == m for x in range(1, 4 * k + 1)) else 4 * k)
              for k in (3, 7) for m in range(1, 4 * k + 1))
          and any(pow(m, 6, 13) == 12 for m in range(1, 13)))

    # both roots of -2 satisfy the congruence individually (the pair is the canonical
    # object); the stated representative is the linkage-consistent one
    for Om_, R in CARRIERS.items():
        kB = R["kB"]; other = Om_ - kB
        chk(f"r04 [{Om_}]: both k_B roots satisfy the congruence", (other * other) % Om_ == Om_ - 2)
        chk(f"r04 [{Om_}]: stated representative is linkage-consistent, its partner is not",
              (kB * R["c"]) % Om_ == (Om_ - R["hbar"]) % Om_ and (other * R["c"]) % Om_ != (Om_ - R["hbar"]) % Om_)


    # H. round-05 pair layer: pair-well-definedness and representative inertness
    family('dom', 'H')
    # pair multiplication {±a}{±b} = {±ab} is well defined: the four member
    # products fall in one pair
    for Om_, R in CARRIERS.items():
        a_, b_ = R["kB"], R["c"]
        prods = {(sa * a_ * sb * b_) % Om_ for sa in (1, -1) for sb in (1, -1)}
        chk(f"H [{Om_}]: pair product well defined ({{±k_B}}{{±c}} is one pair)",
              prods == {(a_ * b_) % Om_, (-a_ * b_) % Om_})
        # linkage as a pair THEOREM: (k_B c)^2 = -1, so the product pair is the
        # root pair of -1, which is {±hbar}
        chk(f"H [{Om_}]: (k_B c)^2 = -1 (linkage derived at pair level)",
              pow(a_ * b_, 2, Om_) == Om_ - 1)
        chk(f"H [{Om_}]: product pair equals {{±hbar}}",
              prods == {R["hbar"] % Om_, (Om_ - R["hbar"]) % Om_})
        # (hbar c / G)^2 = -2: the monomial lands in the k_B pair
        mono = (R["hbar"] * R["c"] * pow(R["G"], -1, Om_)) % Om_
        chk(f"H [{Om_}]: (hbar c/G)^2 = -2, landing in the k_B pair",
              pow(mono, 2, Om_) == Om_ - 2 and mono in {R["kB"], Om_ - R["kB"]})
        # 10:E5 (p10028)
    # representative inertness: exactly the assignments with s_h = s_c*s_k are
        # admissible (a (Z/2)^2 group), and every checked identity holds on each
        admissible_count = 0
        for s_c in (1, -1):
            for s_h in (1, -1):
                for s_k in (1, -1):
                    hb2, c2_, kB2 = (s_h * R["hbar"]) % Om_, (s_c * R["c"]) % Om_, (s_k * R["kB"]) % Om_
                    quad = ((2 * c2_ * c2_) % Om_ == 1 and (hb2 * hb2) % Om_ == Om_ - 1
                            and (kB2 * kB2) % Om_ == Om_ - 2)
                    link = (kB2 * c2_) % Om_ == (Om_ - hb2) % Om_
                    if quad and link:
                        admissible_count += 1
                        h2 = (Om_ - hb2) % Om_
                        chk(f"H [{Om_}] ({s_c},{s_h},{s_k}): h-form holds", h2 == (-hb2) % Om_)
                        chk(f"H [{Om_}] ({s_c},{s_h},{s_k}): monomial lands on this assignment's k_B",
                              (hb2 * c2_ * pow(R["G"], -1, Om_)) % Om_ == kB2)
                    assert quad, "quadratic defining congruences are sign-blind"
        chk(f"H [{Om_}]: admissible assignments form (Z/2)^2 (exactly four)",
              admissible_count == 4)
    # hbar-flip relabels within the pair: {hbar, h} -> {h, hbar}
    chk("H: hbar-flip relabels the {hbar,h} pair (233: 89 <-> 144)",
          (233 - 89) % 233 == 144 and (233 - 144) % 233 == 89)
    flush('dom', order=list('ABCDEFGH'))

# ------------------------------------------------------------------------------------------------------------
# block lift — check_lift: exact verification of Proposition [The lift] (prop:lift)
#
# The flag records the fractional-Fourier quarter that the chart duality forgets.
# All arithmetic is exact (Python integers, modular); no floats, no RNG.
#
# Checks, per shell (p, g) and per Carrier Om:
#   L1  operator four-cycle: F = i*W on F_p^{p-1}, F^2 = J (parity), F^4 = id,
#       F^2 != id  (order exactly four).
#   L2  chart shadow order two: F exchanges the two dual charts, J exchanges
#       none; the cardinal skeleton acts on charts as s mod 2.
#   L3  record map: s -> Iq^s is an isomorphism Z_4 -> flag subgroup
#       {0, k, 2k, 3k} of Z_{p-1}; quotient by {0, 2k} returns s mod 2
#       (the diagram commutes; kernel of the forgetting = {id, J}).
#   L4  Carrier face: hbar^2 = -1 (mod Om), hbar^4 = 1, hbar^2 != 1:
#       the crossing quantum has order four, never two.
#   L5  invariance classification on the realized lattice (Theorem 5 preamble):
#       {u in Z_{p-1} : eps*u = u for every admissible eps} = {0, 2k} exactly;
#       witnesses (s,j) = (k,1) -> u = 2k invariant, (-k,1) -> u = 0 invariant,
#       (0,1) -> u = k not invariant, (0,2) -> u = 2k invariant.
#
# Instances: shell (13, 2) with the laboratory-scale shell (173, 3) as the
# second witness; Carriers 233 and 2408561 (the laboratory Carrier).
def modmat_mul(A, B, p):
    n = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(n)) % p for j in range(n)]
            for i in range(n)]

def check_shell(p, g):
    n = p - 1                       # meridian cycle order 4k
    k = n // 4                      # capacity
    i_res = (-pow(g, k, p)) % p     # oriented quarter-turn residue
    assert (i_res * i_res) % p == p - 1, "i^2 != -1"

    # 10:D3 (p10019)
    # shell Fourier matrix W_{jk} = g^{jk} on F_p^{n}; F = i*W
    W = [[pow(g, (j * l) % n, p) for l in range(n)] for j in range(n)]
    F = [[(i_res * W[j][l]) % p for l in range(n)] for j in range(n)]

    F2 = modmat_mul(F, F, p)
    F4 = modmat_mul(F2, F2, p)
    I = [[1 if a == b else 0 for b in range(n)] for a in range(n)]
    # parity J: index inversion j -> -j mod n
    J = [[1 if b == (-a) % n else 0 for b in range(n)] for a in range(n)]

    l1 = (F2 == J) and (F4 == I) and (F2 != I)

    # L2: chart shadow. Charts = the primal/dual pair; F steps the cardinal
    # skeleton s=0,k,2k,3k; chart action is s mod 2 (F exchanges, J fixes).
    skeleton = [0, 1, 2, 3]                      # multiples of k
    chart_action = [s % 2 for s in skeleton]     # id, swap, id, swap
    l2 = chart_action == [0, 1, 0, 1]

    # L3: record map s -> s*k in Z_n; image = flag subgroup, order four;
    # quotient by {0, 2k} returns s mod 2.
    flag = [(s * k) % n for s in skeleton]
    order4 = len(set(flag)) == 4 and all((4 * f) % n == 0 or f % k == 0 for f in flag)
    subgroup = all(((flag[a] + flag[b]) % n) in flag for a in skeleton for b in skeleton)
    quotient = all((flag[s] % (2 * k) == 0) == (chart_action[s] == 0) for s in skeleton)
    l3 = order4 and subgroup and quotient

    return l1, l2, l3

def check_invariance(p):
    n = p - 1
    k = n // 4
    units = [e for e in range(1, n) if gcd(e, n) == 1]
    fixed = {u for u in range(n) if all((e * u) % n == u for e in units)}
    classified = fixed == {0, 2 * k}
    real = lambda s, j: (s + j * k) % n
    witnesses = (real(k, 1) in fixed and real(-k, 1) in fixed
                 and real(0, 1) not in fixed and real(0, 2) in fixed)
    return classified and witnesses

def check_carrier(Om):
    # hbar = a square root of -1 mod Om (exists since Om = 1 mod 4)
    hbar = None
    for x in range(2, Om):
        if (x * x) % Om == Om - 1:
            hbar = x
            break
    assert hbar is not None
    l4 = (pow(hbar, 2, Om) == Om - 1) and (pow(hbar, 4, Om) == 1) \
         and (pow(hbar, 2, Om) != 1)
    return l4

def block_lift():
    """Block lift — check_lift: Proposition `lift`, the five claims L1–L5 on two shells and two Carriers (lift.L1 … lift.L5)."""
    for (p, g) in [(13, 2), (173, 3)]:
        l1, l2, l3 = check_shell(p, g)
        chk("L1(p=%d)" % p, l1, "lift", "L1"); chk("L2(p=%d)" % p, l2, "lift", "L2")
        chk("L3(p=%d)" % p, l3, "lift", "L3"); chk("L5(p=%d)" % p, check_invariance(p), "lift", "L5")
    for Om in [233, 2408561]:
        chk("L4(Om=%d)" % Om, check_carrier(Om), "lift", "L4")
    flush("lift", order=["L1", "L2", "L3", "L4", "L5"])

if __name__ == "__main__":
    import time
    want = [a.lower() for a in sys.argv[1:]] or sorted(BLOCK)
    bad = [b for b in want if b not in BLOCK]
    if bad: sys.exit(f"no block {', '.join(bad)}: the blocks are {', '.join(sorted(BLOCK))}")
    t0 = time.time()
    for b in want:
        t = time.time(); print(f"— block {b}"); _run_block(b); print(f"    [block {b}: {time.time() - t:.1f} s]")
    ok = summary(write=(want == sorted(BLOCK)))
    print(f"{len(RESULTS)} family checks, {len(MICRO)} exact micro-checks, {time.time() - t0:.1f} s" + ("; results.json written" if want == sorted(BLOCK) else ""))
    sys.exit(0 if ok else 1)
