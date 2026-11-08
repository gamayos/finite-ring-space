#!/usr/bin/env python3
"""The core for the live editor (no imports, no Mathlib), one self-contained file each:
web/FrcCore.lean — the whole library in dependency order (the FRC-wide copy); web/core/<Module>.lean — one paper's
module (or the master ledger's, Master) with the modules it rests on inlined, ending in a `-- Ledger predicates: axioms` block, one `#print axioms` per
predicate declaration of the module, so the editor computes each predicate's axioms in front of the reader; the same for
each key file (web/core/Keys.<Theme>.lean, one `#print axioms` per key). --check compares."""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent
ORDER = ["Nat", "Pigeonhole", "Shell", "Series", "Cycle", "Ring", "FrameCore", "Frame", "Parity", "Transform", "Orbit", "Sum", "Theme.Projective", "Theme.Fourier", "Theme.Fractional", "Theme.Lifts", "Theme.Dichotomy", "Theme.Rotations", "Theme.Heisenberg", "Theme.Spectra", "Theme.Exclusivity", "Theme.Shift", "Theme.Quadratic", "Theme.Extension", "Theme.Domain", "Theme.Spin", "Theme.Lorentz", "Theme.Register", "Theme.Numbers", "Theme.Logic", "Theme.SecondOrder", "Theme.Formation", "Theme.Reach", "Theme.Diagonal", "Theme.Threshold", "Theme.Sets", "Theme.Equivariant", "Theme.Transfer", "Theme.Field", "Theme.Foundation", "Theme.Drive", "Theme.Framed", "Theme.Quaternion", "Theme.Carrier", "Theme.Subject", "Theme.Pair", "Theme.Hopf", "Theme.Symbol", "Theme.Gravity", "Theme.Lattice", "Theme.Drift", "Theme.Relaxation", "Theme.Window", "Theme.Static", "Theme.Quantum", "Theme.Observation", "Theme.Interference", "Theme.Composite", "Theme.Unitary", "Theme.Interactions", "Theme.Fields", "Theme.Horizon", "Theme.Zeros", "Theme.Ladder", "Theme.Flavour", "Theme.Dark", "Theme.Hadrons", "Theme.Super", "Theme.Brackets", "Theme.YangMills", "Theme.Strata", "Theme.Calibration", "Theme.Tally", "Theme.Causal", "Meridian", "Fourier", "Algebra", "Epi", "Dimensions", "Poly", "Quaternion", "Causality", "Representation", "Reductio", "Godel", "Finitism", "Geometry", "Complex", "Instances", "Theme.Dirac", "Theme.Packed", "Theme.Plane", "Theme.Hermitian", "Theme.Operator", "Theme.Unipotent", "Theme.Spinor", "Theme.Loss", "Theme.Det", "Theme.Elim", "Theme.Cayley", "Theme.Product", "Theme.Poly", "Theme.CharPoly", "Rh", "Entropy", "Gravity", "Dirac", "S13", "Quantum", "Pnp", "Fields", "Flavour", "Dark", "Hadrons", "Spacetime", "YangMills"]
ORDER += ["Keys." + p.stem for p in sorted((ROOT / "FrcCore" / "Keys").glob("*.lean"))]   # the key files (make_keys.py, task LM19): after the themes they import
ORDER += ["Master"]                                                                       # the master ledger's named predicate declarations (make_master.py, 8 November 2026): aliases of the keys, after the key files
_IMPORTED = re.findall(r"^import FrcCore\.([\w.]+)", (ROOT / "FrcCore.lean").read_text(encoding="utf-8"), re.M)
_MISSING = sorted(set(_IMPORTED) - set(ORDER))
assert not _MISSING, f"make_core_web.py: modules imported by FrcCore.lean and absent from ORDER (ticket T13): {_MISSING}"   # 8 November 2026
PAPERS = ["Algebra", "Fourier", "Geometry", "Causality", "Representation", "Reductio", "Godel", "Finitism", "Epi", "Dimensions", "Rh", "Entropy", "Gravity", "Dirac", "S13", "Quantum", "Pnp", "Fields", "Flavour", "Dark", "Hadrons", "Spacetime", "YangMills"]   # the modules that are a paper's (Quantum: 22-quantum, 15 October 2026, the module Qm until 21 October 2026; Pnp: 26-pnp, 16 October 2026; Fields: 27-fields, 16 October 2026; Flavour: 28-flavour, 17 October 2026; Dark: 32-dark, 18 October 2026; Spacetime: 7-spacetime, 31 October 2026; YangMills: 46-yangmills, 8 November 2026)

def src(m): return (ROOT / "FrcCore" / f"{m.replace('.', '/')}.lean").read_text(encoding="utf-8")   # Theme.Logic: FrcCore/Theme/Logic.lean
def _topo(order):
    """ORDER in dependency order: a module after every module it imports (the listed order otherwise kept)."""
    out, seen = [], set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in re.findall(r"^import FrcCore\.([\w.]+)", src(m), re.M): visit(d)
        out.append(m)
    for m in order: visit(m)
    return out
ORDER = _topo(ORDER)
def body(m): return "\n".join(l for l in src(m).splitlines() if not l.startswith("import "))
def imports(m): return re.findall(r"^import FrcCore\.([\w.]+)", src(m), re.M)
def closure(m, seen=None):
    seen = set() if seen is None else seen
    for d in imports(m):
        if d not in seen: seen.add(d); closure(d, seen)
    return seen
def rows(m):
    """The predicate declarations of a module, fully qualified: those of a generated ledger section (make_predicates.py; named
    by the rows' declared names since 6 November 2026, else by their keys) and the keyed theorems of a key file (p<key>). A
    namespace walk (a module may host another paper's predicates in a `namespace FRC.<Paper>` block at its end, as
    Quaternion hosts 1-algebra's G5)."""
    stack, out, insec = [], [], False
    for line in src(m).splitlines():
        if line.startswith("-- Ledger predicates of "): insec = True
        elif line.startswith("-- end ledger predicates"): insec = False
        mm = re.match(r"^namespace\s+(\S+)", line)
        if mm: stack.append(mm.group(1)); continue
        mm = re.match(r"^end\s+(\S+)", line)
        if mm and stack and stack[-1] == mm.group(1): stack.pop(); continue
        mm = re.match(r"^(?:theorem|def) ([A-Za-z_][A-Za-z0-9_']*)", line)
        if mm and (insec or re.fullmatch(r"p\d{5}", mm.group(1))): out.append(".".join(stack + [mm.group(1)]))
    return out

def whole():
    out = ["/-! FrcCore — the FRC substrate from first principles, one file for the live instance (no Mathlib,\n"
           "no axioms). Generated from FrcCore/*.lean in dependency order (" + ", ".join(ORDER) + ")\n"
           "by make_core_web.py; the modules' own headers follow. Check any declaration with `#print axioms`. -/\n"]
    for m in ORDER: out.append(f"\n/-! inlined: FrcCore/{m.replace('.', '/')}.lean -/\n" + body(m) + "\n")
    return "".join(out)

def paper(m):
    mods = [x for x in ORDER if x in closure(m)]
    out = [f"/-! FrcCore/{m.replace('.', '/')}.lean for the live instance: the core module with the {len(mods)} modules it rests on inlined\n"
           f"({', '.join(mods)}); plain Lean, no Mathlib, no axioms. Generated by make_core_web.py — edit the modules, not this file.\n"
           f"The ledger predicates are the declarations at the end of the module, named by their rows' declared names (`no_definite_space`) or by their accession keys (`p10015`), the key in each docstring; their axioms are printed below them. -/\n"]
    for x in mods: out.append(f"\n/-! inlined: FrcCore/{x.replace('.', '/')}.lean -/\n" + body(x) + "\n")
    out.append(f"\n/-! FrcCore/{m.replace('.', '/')}.lean -/\n" + body(m) + "\n")
    rs = rows(m)
    if rs: out.append("\n-- Ledger predicates: axioms (each predicate's, computed here)\n" + "".join(f"#print axioms {r}\n" for r in rs))
    return "".join(out)

targets = {ROOT / "web" / "FrcCore.lean": whole()}
(ROOT / "web" / "core").mkdir(parents=True, exist_ok=True)
for m in sorted(set(PAPERS) | {x for x in ORDER if rows(x)}, key=ORDER.index): targets[ROOT / "web" / "core" / f"{m}.lean"] = paper(m)   # every paper's module, and every module hosting predicate declarations
if "--check" in sys.argv:
    stale = [str(p.relative_to(ROOT)) for p, t in targets.items() if not p.exists() or p.read_text(encoding="utf-8") != t]
    sys.exit(f"stale: {', '.join(stale)} — run make_core_web.py" if stale else 0)
for p, t in targets.items(): p.write_text(t, encoding="utf-8"); print(f"{p.relative_to(ROOT)}: {len(t.splitlines())} lines")
