#!/usr/bin/env python3
"""The zero-axiom gate of FrcCore (run from lean/, the lake package root).

Collects every `theorem`, `def` and `instance` of FrcCore/*.lean (namespace-aware), generates
`CoreAxioms.lean` with one `#print axioms` per declaration, runs it under `lake env lean`, writes
FrcCore/axioms.log, and fails unless every line reads "does not depend on any axioms".
Usage: python3 check_core_axioms.py [--log-only]
"""
import re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MODULES = ["Nat", "Pigeonhole", "Shell", "Frame", "Orbit", "Sum", "Meridian", "Algebra", "Epi", "Poly", "Quaternion", "Causality", "Representation", "Reductio", "Geometry", "Complex", "Instances"]

def declarations(path):
    stack, out = [], []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^namespace\s+(\S+)", line)
        if m: stack.append(m.group(1)); continue
        m = re.match(r"^end\s+(\S+)", line)
        if m and stack and stack[-1] == m.group(1): stack.pop(); continue
        m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)?(theorem|def|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)", line)
        if m:
            out.append(".".join(stack + [m.group(2)]))
    return out

decls = []
for mod in MODULES:
    decls += declarations(ROOT / "FrcCore" / f"{mod}.lean")
ax = ROOT / "CoreAxioms.lean"
ax.write_text("import FrcCore\n" + "".join(f"#print axioms {d}\n" for d in decls), encoding="utf-8")
res = subprocess.run(["lake", "env", "lean", str(ax)], cwd=ROOT, capture_output=True, text=True)
lines = [l for l in (res.stdout + res.stderr).splitlines() if l.strip()]
log = ROOT / "FrcCore" / "axioms.log"
log.write_text("\n".join(lines) + "\n", encoding="utf-8")
bad = [l for l in lines if "does not depend on any axioms" not in l]
print(f"{len(decls)} declarations; {len(lines) - len(bad)} with no axioms; {len(bad)} other lines")
for l in bad: print("  ", l)
if "--log-only" in sys.argv: sys.exit(0)
sys.exit(1 if bad or res.returncode else 0)
