#!/usr/bin/env python3
"""The zero-axiom gate of FrcCore, gate G11 (run from lean/, the lake package root).

Collects every `theorem`, `def` and `instance` of the modules under FrcCore/ (namespace-aware), discovered rather than
listed (ledger migration, task LM21): the modules the root FrcCore.lean imports, in its order, then every other module
under FrcCore/ by path (the ledgers' certificates, and any module the root misses); then the bridges under FrcBridge/
(task LM34, from LM22), which rest on the core alone. Generates `CoreAxioms.lean`, which imports them, with one
`#print axioms` per declaration; runs it under `lake env lean`; writes FrcCore/axioms.log; and fails unless every line
reads "does not depend on any axioms".
Usage: python3 check_core_axioms.py [--log-only]
"""
import re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def modules():
    """The modules under FrcCore/ (Theme/Logic), the root's imports first in its order, then the rest by path."""
    base = ROOT / "FrcCore"
    found = sorted(str(p.relative_to(base))[:-5] for p in base.rglob("*.lean") if "_to_delete" not in p.relative_to(base).parts)
    root = [m.replace(".", "/") for m in re.findall(r"^import FrcCore\.([\w.]+)", (ROOT / "FrcCore.lean").read_text(encoding="utf-8"), re.M)]
    return [m for m in root if m in found] + [m for m in found if m not in root], set(root)

MODULES, IN_ROOT = modules()
BRIDGES = sorted(str(p.relative_to(ROOT / "FrcBridge"))[:-5] for p in (ROOT / "FrcBridge").rglob("*.lean")
                 if "_to_delete" not in p.parts) if (ROOT / "FrcBridge").is_dir() else []

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

decls, extra = [], []
for mod in MODULES:
    ds = declarations(ROOT / "FrcCore" / f"{mod}.lean")
    if ds and mod not in IN_ROOT: extra.append(mod)
    decls += ds
for mod in BRIDGES: decls += declarations(ROOT / "FrcBridge" / f"{mod}.lean")
ax = ROOT / "CoreAxioms.lean"
ax.write_text("import FrcCore\n" + "".join(f"import FrcCore.{m.replace('/', '.')}\n" for m in extra)
              + "".join(f"import FrcBridge.{m.replace('/', '.')}\n" for m in BRIDGES) + "".join(f"#print axioms {d}\n" for d in decls), encoding="utf-8")
res = subprocess.run(["lake", "env", "lean", str(ax)], cwd=ROOT, capture_output=True, text=True)
lines = [l for l in (res.stdout + res.stderr).splitlines() if l.strip()]
log = ROOT / "FrcCore" / "axioms.log"
log.write_text("\n".join(lines) + "\n", encoding="utf-8")
bad = [l for l in lines if "does not depend on any axioms" not in l]
print(f"{len(MODULES)} modules discovered, {len(BRIDGES)} bridge module(s); {len(decls)} declarations; {len(lines) - len(bad)} with no axioms; {len(bad)} other lines")
for l in bad: print("  ", l)
if "--log-only" in sys.argv: sys.exit(0)
sys.exit(1 if bad or res.returncode else 0)
