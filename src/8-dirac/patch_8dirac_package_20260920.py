#!/usr/bin/env python3
"""The 8-dirac chain, 20 Sep 2026 — the package-side patches (finite-ring-space/src/8-dirac).

Exact-match patches; run from finite-ring-space/src/8-dirac/ (dry run by default; `--apply` writes, with a
pre-edit copy of each file in `_to_delete/`).  (1) The registry `dcommon.py` names the three families the run
emits but the registry did not know — `o2.C3i`, `o2.C3a` (the square classes of `i` and of `2`, `2⁻¹`, `−2`,
rows 8:B3) and `o8.X9` (the dispersion relation on the cycle, row 8:F4) — and drops the never-emitted `o2.C3`,
so that every record of `results.json` carries its rows and label and the family count reads 52 everywhere;
(2) the README's block list reads A–F, V, T (block O was renamed T on 18 Sep) and gains the Lean sentence;
(3) `make_notebook.py` gains the Lean sentence.  Then: `python3 run_all.py` and `python3 make_notebook.py`.
"""
import sys, hashlib, shutil
from pathlib import Path

APPLY = "--apply" in sys.argv

def patch(path, pairs):
    p = Path(path); s = p.read_text(encoding="utf-8"); before = hashlib.md5(s.encode()).hexdigest()
    for old, new in pairs:
        n = s.count(old)
        if n != 1: sys.exit(f"{path}: pattern matched {n} times, expected 1:\n{old[:160]}")
        s = s.replace(old, new)
    if APPLY:
        bak = p.parent / "_to_delete" / (p.name + ".pre-chain-20260920")
        if not (p.parent / "_to_delete").exists(): (p.parent / "_to_delete").mkdir()
        shutil.copy2(p, bak)
        p.write_text(s, encoding="utf-8")
    print(f"{path}: {len(pairs)} replacements ({before} -> {hashlib.md5(s.encode()).hexdigest()}){'' if APPLY else ' [dry run]'}")

LEAN = ("Where a row is proved in Lean (`lean/FrcCore/Dirac.lean` with no axioms, or `lean/FrcLedger/Dirac.lean` on Mathlib —\n"
        "the chronon parity and the named residues, the Hermitian layer and the Cayley step, the kinetic period, the torus with\n"
        "Hilbert 90, the Clifford relations and the spinor twist, the characters and the counts), the check here is the instance\n"
        "the reader can run. ")

patch("dcommon.py", [
('    "o2.C1": "8:B3", "o2.C2": "8:B2", "o2.C3": "8:B3", "o2.C4": "8:B3", "o2.C5": "8:B3", "o2.C6": "8:D5",',
 '    "o2.C1": "8:B3", "o2.C2": "8:B2", "o2.C3i": "8:B3", "o2.C3a": "8:B3", "o2.C4": "8:B3", "o2.C5": "8:B3", "o2.C6": "8:D5",'),
('    "o8.X1": "8:D9", "o8.X2": "8:D9", "o8.X3": "8:D9", "o8.X4": "8:D9", "o8.X5": "8:D10", "o8.X6": "8:D10", "o8.X7": "8:F4", "o8.X8": "8:D11",',
 '    "o8.X1": "8:D9", "o8.X2": "8:D9", "o8.X3": "8:D9", "o8.X4": "8:D9", "o8.X5": "8:D10", "o8.X6": "8:D10", "o8.X7": "8:F4", "o8.X8": "8:D11",\n    "o8.X9": "8:F4",'),
('    "o2.C3": "i, 2, 2⁻¹, −2 are squares iff κ is even: on κ-even shells g is the only named nonsquare",',
 '    "o2.C3i": "i = g^{−κ} is a square iff κ is even (8 | p − 1), on every symmetry-complete shell p < 2000",\n'
 '    "o2.C3a": "2, 2⁻¹, −2 are squares iff κ is even: on κ-even shells g is the only named nonsquare",'),
('    "o8.X8": "spin lift vs the spinor form: S(x,y)# = S(x,−y) = δS⁻¹; the transport scales the X-form by N(z), norm-one lifts preserve it",',
 '    "o8.X8": "spin lift vs the spinor form: S(x,y)# = S(x,−y) = δS⁻¹; the transport scales the X-form by N(z), norm-one lifts preserve it",\n'
 '    "o8.X9": "the dispersion relation on the cycle: −Δ_Φ χ_k = (2 − g^k − g^{−k}) χ_k for every k (F_13); D^s − m invertible for m ≠ 0",'),
])

patch("README.md", [
("paper's predicate ledger it witnesses (the paper's Section \"Machine verification and predicate ledger\", 46 rows in\nblocks A–F, V, O, cited as `8:XN`; public copy `docs/8-dirac/8-dirac-ledger.html`); the ledger's source column cites\nthe check ids in return. Master-ledger rows",
 "paper's predicate ledger it witnesses (the paper's Section \"Machine verification and predicate ledger\", 47 rows in\nblocks A–F, V, T, cited as `8:XN`; public copy `docs/8-dirac/8-dirac-ledger.html`); the ledger's source column cites\nthe check ids in return. " + LEAN + "Master-ledger rows"),
("| `o2_checks.py` | o2.C1–C9 | 1048 |", "| `o2_checks.py` | o2.C1, C2, C3i, C3a, C4–C9 | 1048 |"),
("| `o8_checks.py` | o8.X1–X8 | 55 |", "| `o8_checks.py` | o8.X1–X9 | 55 |"),
("V1–V3 the\nverification rows; T1 the open classification of the admissible set (a task, block T).",
 "V1–V4 the\nverification rows (V4 the two Lean libraries, 20 Sep 2026); T1 the open classification of the admissible set (a task, block T)."),
])

patch("make_notebook.py", [
("`8:XN`; public copy at `docs/8-dirac/8-dirac-ledger.html`), and the ledger's source column cites the check ids in return. The\nmaster-ledger rows",
 "`8:XN`; public copy at `docs/8-dirac/8-dirac-ledger.html`), and the ledger's source column cites the check ids in return. " + LEAN + "The\nmaster-ledger rows"),
])
print("done" + ("" if APPLY else " (dry run; pass --apply to write)"))
