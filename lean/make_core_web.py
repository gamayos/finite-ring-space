#!/usr/bin/env python3
"""web/FrcCore.lean: the core in one file for the live editor (no imports, no Mathlib). --check compares."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent
ORDER = ["Nat", "Pigeonhole", "Shell", "Frame", "Orbit", "Sum", "Algebra", "Poly", "Quaternion", "Causality", "Representation", "Reductio", "Geometry", "Complex", "Instances"]
out = ["/-! FrcCore — the FRC substrate from first principles, one file for the live instance (no Mathlib,\n"
       "no axioms). Generated from FrcCore/*.lean in the order Nat, Pigeonhole, Shell, Frame, Orbit, Sum,\n"
       "Algebra, Geometry, Instances by make_core_web.py; the modules' own headers follow. Check any declaration with `#print axioms`. -/\n"]
for m in ORDER:
    src = (ROOT / "FrcCore" / f"{m}.lean").read_text(encoding="utf-8")
    body = "\n".join(l for l in src.splitlines() if not l.startswith("import "))
    out.append(f"\n/-! inlined: FrcCore/{m}.lean -/\n" + body + "\n")
text = "".join(out); target = ROOT / "web" / "FrcCore.lean"
if "--check" in sys.argv:
    sys.exit(0 if target.exists() and target.read_text(encoding="utf-8") == text else ("web/FrcCore.lean is stale: run make_core_web.py", 1)[1])
target.write_text(text, encoding="utf-8"); print(f"web/FrcCore.lean: {len(text.splitlines())} lines")
