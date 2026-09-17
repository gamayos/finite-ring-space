#!/usr/bin/env python3
"""check_axioms.py — the axioms gate for the ledger's Lean witnesses (strict rule).

1. Collects every `theorem`/`lemma`/`def`/`abbrev` declared in FrcLedger/*.lean (namespace-aware) and writes
   Axioms.lean: one `#print axioms` per declaration.
2. Runs `lake env lean Axioms.lean`, writes the output to axioms.log (one line per declaration).
3. Fails unless every declaration depends on a subset of {propext, Classical.choice, Quot.sound}.
   `sorryAx` (an unfinished proof), `Lean.ofReduceBool` (native_decide), `Lean.trustCompiler` and any
   other axiom are failures — red, never amber.

    python3 check_axioms.py            # generate, run, gate
    python3 check_axioms.py --log-only # gate an existing axioms.log without running Lean
"""
import re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma|def|abbrev)\s+([\w.']+)", re.M)
NS = re.compile(r"^(namespace|end)\s+([\w.]+)\s*$", re.M)
LINE = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")

def declarations(path):
    """Fully qualified theorem names of one module, in source order."""
    out, stack = [], []
    for m in re.finditer(r"^(namespace|end)\s+([\w.]+)\s*$|^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma|def|abbrev)\s+([\w.']+)", path.read_text(encoding="utf-8"), re.M):
        if m.group(1) == "namespace": stack.append(m.group(2))
        elif m.group(1) == "end":
            if stack and stack[-1] == m.group(2): stack.pop()
        elif m.group(3):
            out.append(".".join(stack + [m.group(4)]))
    return out

def gate(log_text):
    bad, n = [], 0
    for line in log_text.splitlines():
        m = LINE.match(line.strip())
        if not m: continue
        n += 1
        axioms = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
        extra = axioms - ALLOWED
        if extra: bad.append((m.group(1), sorted(extra)))
    return n, bad

def main():
    if "--log-only" not in sys.argv:
        names = [d for f in sorted((ROOT / "FrcLedger").glob("*.lean")) for d in declarations(f)]
        (ROOT / "Axioms.lean").write_text("import FrcLedger\n" + "".join(f"#print axioms {n}\n" for n in names), encoding="utf-8")
        print(f"Axioms.lean: {len(names)} declarations")
        r = subprocess.run(["lake", "env", "lean", "Axioms.lean"], cwd=ROOT, capture_output=True, text=True)
        (ROOT / "axioms.log").write_text(r.stdout, encoding="utf-8")
        if r.returncode != 0:
            sys.exit(f"lake env lean Axioms.lean failed:\n{r.stderr[-2000:]}")
    n, bad = gate((ROOT / "axioms.log").read_text(encoding="utf-8"))
    print(f"axioms.log: {n} declarations checked against {sorted(ALLOWED)}")
    tiers = {0: 0, 1: 0, 2: 0}
    for line in (ROOT / "axioms.log").read_text(encoding="utf-8").splitlines():
        m = re.match(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", line.strip())
        if not m: continue
        ax = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
        tiers[0 if not ax else 1 if ax <= {"propext", "Quot.sound"} else 2] += 1
    print(f"tiers: {tiers[0]} with no axioms (tier 0), {tiers[1]} extensionality only (tier 1), {tiers[2]} classical (tier 2); the zero-axiom library is FrcCore (check_core_axioms.py)")
    for name, extra in bad: print(f"  FAIL {name}: {', '.join(extra)}")
    if bad: sys.exit(1)
    if n == 0: sys.exit("no declarations found")
    print("axioms gate: PASS")

if __name__ == "__main__":
    main()
