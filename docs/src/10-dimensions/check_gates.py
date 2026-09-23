#!/usr/bin/env python3
"""check_gates.py -- grep gates for the 10-dimensions refactor.

Run from the paper root. Exit nonzero on any gate failure.
Gates: blacklist tokens, the kappa/tau/t role gates, revision-markup
residue, and the constructive register.
"""

import re, sys, glob

fail = 0

def gate(name, ok, detail=""):
    global fail
    mark = "PASS" if ok else "FAIL"
    print(f"[{mark}] {name}" + (f" -- {detail}" if detail else ""))
    if not ok:
        fail += 1

sources = sorted(glob.glob("sections/*.tex")) + ["mdpi.tex"]
text = {f: open(f).read() for f in sources}
allt = "\n".join(text.values())

# 1. revision-markup residue: none may survive
for pat in (r"\\changestart", r"\\changeend", r"\\chgtext", r"diffbuild", r"sidebarcolor"):
    hits = re.findall(pat, allt)
    gate(f"markup residue x0: {pat}", len(hits) == 0, f"{len(hits)}")

# 2. role gates: kappa / tau / t
role_patterns = [
    (r"\\chron\}\{t\}", "\\chron defined as t"),
    (r"\\chron\s*=\s*\\kap", "chronon equated to capacity"),
    (r"temporal frame label", "tau as 'temporal frame label'"),
    (r"temporal phase step", "g as 'temporal phase step'"),
    (r"tick,? containing \\?\(?\\kap", "kappa as duration (tick containing kappa)"),
    (r"packet tick", "packet-tick temporalisation"),
    (r"temporal unit is one cardinal", "cardinal tick as temporal unit"),
]
for pat, label in role_patterns:
    hits = re.findall(pat, allt)
    gate(f"role gate x0: {label}", len(hits) == 0, f"{len(hits)}")

# 3. blacklist (corpus standard)
blacklist = [r"seat", r"phase carrier", r"h *= *\(2G\)", r"\\hbar *= *\\It", r"G *= *1/4\\pi",
             r"Z/\(", r"total entropy", r"carrier-internal", r"Carrier's drive"]
for pat in blacklist:
    hits = re.findall(pat, allt)
    gate(f"blacklist x0: {pat}", len(hits) == 0, f"{len(hits)}")

# 4. constructive register: no referee-facing prose in the manuscript
for pat in (r"this version", r"the reviewer", r"in response to", r"revised version",
            r"we now correct", r"earlier draft"):
    hits = re.findall(pat, allt, re.I)
    gate(f"constructive register x0: '{pat}'", len(hits) == 0, f"{len(hits)}")

# 5. required forms present
gate("frame written (\\chron;0,1,\\gen)", r"(\chron;0,1,\gen)" in allt or "\\chron;0,1,\\gen" in allt)
gate("Object frame (t;q,k,v) present", "\\dt;q,k,v" in allt or "(\\dt;\\,q,k,v" in allt or "\\dt;\\,q" in allt)
gate("phase-cycle order stated capacity-first (4kap=2pi=p-1)", "4\\kap=2\\pi=\\p-1" in allt)
# capacity-first discipline: 'symmetry-complete' invoked exactly once, at first use
sc = len(re.findall(r"symmetry-complete", allt))
gate("'symmetry-complete' invoked exactly once", sc == 1, f"count = {sc}")


# 6. round-01 revision gates
rev_required = [
    ("internal flag theorem present", r"contains exactly one subgroup of order four"),
    ("crossing degree defined", r"crossing degree"),
    ("pair form of the defining congruences present", r"root pair of"),
    ("reframing action defined", r"Admissible reframing"),
    ("admissibility triple stated", "pmod3"),
    ("temperature corollary present", r"acceleration domain"),
    ("h-form remark present", r"h-form"),
]
for label, pat in rev_required:
    hits = re.findall(pat, allt)
    gate(f"revision: {label}", len(hits) >= 1, f"{len(hits)}")

rev_banned = [
    ("adjoined to the free lattice", "flag described as adjoined"),
    ("no fifth independent relation exists", "un-narrowed closure phrase"),
    ("m_P^{2}\\equiv\\Om\\equiv0", "untyped m_P^2 congruence"),
    ("over and above its two generators", "flag as extra structure"),
    ("the selection is the lower-half", "half-plane rule asserted as the selection"),
]
for pat, label in rev_banned:
    hits = allt.count(pat)
    gate(f"revision x0: {label}", hits == 0, f"{hits}")


# 7. round-02 gates
r02_required = [
    ("pushforward action named", "pushforward"),
    ("window covariance stated", "Window covariance"),
    ("representative convention stated inert", "inert"),
    ("co-orientation deferred to coupling layers", "o-orientation of a Subject frame"),
    ("positive-root branch stated", "positive square root"),
]
for label, pat in r02_required:
    hits = allt.count(pat)
    gate(f"r02: {label}", hits >= 1, f"{hits}")

r02_banned = [
    ("multiplies the coefficient by the scale character $m^{-r}\\eps^{-s}$", "field-character eps action"),
    ("verbatim, as a congruence", "both-face verbatim claim"),
    ("The two imports are irreducible to internal residue-class predicates, and one exact fact shows why", "over-broad irreducibility claim"),
    ("torsion-free labels", "type-wrong label adjective"),
]
for pat, label in r02_banned:
    hits = allt.count(pat)
    gate(f"r02 x0: {label}", hits == 0, f"{hits}")


# 8. round-03 gates
r03_required = [
    ("window bound below half-period", "H<2\\kap"),
    ("sigma-twisted action present", "\\sigma(\\eps)"),
    ("crossed duality defined", "crossed duality"),
    ("count-valued comparison doctrine", "count-valued comparison"),
    ("sub-capacity phrasing", "sub-capacity"),
    ("standing definition of admissibility", "standing definition"),
]
for label, pat in r03_required:
    hits = allt.count(pat)
    gate(f"r03: {label}", hits >= 1, f"{hits}")

r03_banned = [
    ("raises the flag by one", "delta conflation phrase"),
    ("cancels in every observable combination", "unscoped cancellation doctrine"),
    ("inexpressible within any bounded exponent horizon", "loose horizon phrase"),
]
for pat, label in r03_banned:
    hits = allt.count(pat)
    gate(f"r03 x0: {label}", hits == 0, f"{hits}")


# 9. round-04 gates
r04_required = [
    ("pair linkage identity", "pair identity"),
    ("window ladder present", "window ladder"),
    ("coherence window imported", "coherence window"),
    ("atomic chronon remark", "the chronon is atomic"),
    ("equal-crossing-degree scope", "equal crossing degree"),
    ("meridian transport proposition", "Meridian transport onto the flag"),
    ("realisation content restatement", "Proof over the realisation"),
    ("import in table key", "\\tI\\ import"),
]
for label, pat in r04_required:
    hits = allt.count(pat)
    gate(f"r04: {label}", hits >= 1, f"{hits}")

r04_banned = [
    ("then internal, fixed by the cancellation identity", "k_B sign mis-tagged internal"),
    ("imports and one internal identity", "old sign-count phrase"),
    ("every ratio the observer forms between them", "unscoped ratio cancellation"),
    ("chart duality \\(\\delta\\) of Theorem", "caption delta residue"),
    ("\\Theta_P=\\EP/k_B\\)", "signed temperature horizon"),
]
for pat, label in r04_banned:
    hits = allt.count(pat)
    gate(f"r04 x0: {label}", hits == 0, f"{hits}")


# 10. round-05 gates (recentring: pair form; the Carrier layer subordinate)
r05_required = [
    ("defining congruences stated at pair level", "at pair level"),
    ("instantiation subsection present", "Carrier Instantiation"),
    ("Omega-hard thesis sentence present", "registrable manifestation"),
    ("linkage derived not declared", "derived rather than declared"),
    ("minimal-pair figure in the registers section", "smallest admissible scale"),
]
for label, pat in r05_required:
    hits = allt.count(pat)
    gate(f"r05: {label}", hits >= 1, f"{hits}")

r05_banned = [
    ("orientation of \\(\\hbar", "orientation of hbar"),
    ("selects the root", "root-selection language"),
    ("residue reading", "residue reading apparatus"),
    ("declared residue linkage", "linkage as declaration"),
    ("half-plane", "half-plane predicate"),
    ("band rule", "band rule"),
    ("left open here", "manufactured open question"),
    ("minimal-material-mode", "orientation import (hbar)"),
    ("registrability class", "orientation import (c)"),
    ("count positivity", "orientation import ground"),
    ("named imports", "sign-count phrase"),
    ("orientation rule", "orientation-rule layer"),
    ("the signed residue-face reading", "signed-reading phrase"),
]
for pat, label in r05_banned:
    hits = allt.count(pat)
    gate(f"r05 x0: {label}", hits == 0, f"{hits}")

# 11. round-06 gates (the holographic doctrine; bridges retired for realisations)
r06_required = [
    ("new title present", "Dimensional Analysis over Finite Holographic Substrate"),
    ("holographic-substrate remark present", "The holographic substrate"),
    ("encoding condition stated", "encoding condition"),
    ("finite holographic substrate named", "finite holographic substrate"),
    ("realisation legend present", "constitutive rather than interpretive"),
    ("h-form pair named", r"\(h\)-form pair"),
    ("s13 instance cited", "akhtman2026s13"),
]
for label, pat in r06_required:
    hits = allt.count(pat)
    gate(f"r06: {label}", hits >= 1, f"{hits}")

falsifier_count = len(re.findall(r"falsifier", allt))
gate("r06: three falsifiers stated (>=3 mentions)", falsifier_count >= 3, f"{falsifier_count}")

frc_full = len(re.findall(r"Finite Ring Cosmology", allt))
gate("r06: 'Finite Ring Cosmology' expanded exactly once (the primer)", frc_full == 1, f"count = {frc_full}")

r06_banned = [
    (r"\bbridge\b", "bridge as a doctrinal term"),
    (r"bridge-class", "bridge-class label"),
    (r"interpretive content", "interpretive-layer concession"),
    (r"in Finite Ring Cosmology", "old title residue"),
]
for pat, label in r06_banned:
    hits = re.findall(pat, allt, re.I)
    gate(f"r06 x0: {label}", len(hits) == 0, f"{len(hits)}")

sys.exit(1 if fail else 0)




