#!/usr/bin/env python3
"""verify.py — the checks of one revision of the Lean side (run from lean/, the lake package root).

The continuous integration (.github/workflows/lean.yml) compiles every module and every web copy at each push, and it
stays the witness of record. This script runs the same checks on what a revision changed, on a tree that holds its build
products:

1. build      `lake build FrcMathlib FrcCore FrcBridge` and the certificates under FrcCore/Ledgers and FrcMathlib/Ledgers.
              Lake compiles the edited modules and the modules that import them, and nothing else.
2. axioms     check_axioms.py and check_core_axioms.py in full (they take seconds once the libraries are built), then a
              comparison of the four files they write with the committed ones.
3. generated  make_keys.py, make_master.py, make_web.py and make_core_web.py with --check.
4. web        the web copies whose text differs from the base revision, each compiled as a single file, one at a time.
              No other copy is compiled. web/FrcCore.lean holds the whole core and needs more memory than a small
              machine has: it is reported as NOT RUN unless --all-web is given, never as a pass.

    python3 verify.py                  # the working tree against HEAD
    python3 verify.py --base origin/main   # everything since the pushed head
    python3 verify.py --web web/Flavour.lean web/core/Flavour.lean   # these copies, whatever git says
    python3 verify.py --no-web         # steps 1 to 3 only
    python3 verify.py --all-web        # web/FrcCore.lean too

One line per check: PASS, FAIL, CHANGED (a generated file differs from the committed one: commit it) or NOT RUN, with the
seconds it took. The exit code is 0 only when no check failed. On a tree with no build products the first run compiles
every module once (`lake exe cache get` first, for Mathlib).
"""
import argparse, os, shutil, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HEAVY = ["web/FrcCore.lean"]                       # the whole core in one file
AXIOM_FILES = ["axioms.log", "Axioms.lean", "FrcCore/axioms.log", "CoreAxioms.lean"]
GENERATORS = [["make_keys.py", "--docs", "../docs", "--check"], ["make_master.py", "--docs", "../docs", "--check"],
              ["make_web.py", "--check"], ["make_core_web.py", "--check"]]


def tool(name):
    """lake or lean, from PATH or from elan's directory."""
    return shutil.which(name) or str(Path.home() / ".elan" / "bin" / name)


def run(cmd):
    t = time.time()
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr, time.time() - t


def tail(text, n=6):
    lines = [l for l in text.replace("\r", "\n").splitlines() if l.strip()]
    return "\n".join("      " + l[:200] for l in lines[-n:])


class Report:
    def __init__(self):
        self.rows = []

    def add(self, verdict, name, seconds=None, detail=""):
        self.rows.append(verdict)
        took = "" if seconds is None else f"{seconds:7.0f} s"
        print(f"{verdict:8} {name:58} {took}", flush=True)
        if detail:
            print(detail, flush=True)

    def check(self, name, cmd, fails_on_output=None):
        rc, out, sec = run(cmd)
        bad = rc != 0 or (fails_on_output is not None and fails_on_output in out)
        self.add("FAIL" if bad else "PASS", name, sec, tail(out) if bad else "")
        return not bad


def certificates():
    mods = []
    for lib in ("FrcCore/Ledgers", "FrcMathlib/Ledgers"):
        for f in sorted((ROOT / lib).rglob("*.lean")):
            if "_to_delete" not in f.parts:
                mods.append(".".join(f.relative_to(ROOT).with_suffix("").parts))
    return mods


def changed_web(base):
    """The web copies that differ from the base revision, and the new ones."""
    rc, out, _ = run(["git", "diff", "--name-only", base, "--", "web"])
    if rc != 0:
        sys.exit(f"git diff against {base} failed:\n{out}")
    names = [l.strip() for l in out.splitlines() if l.strip()]
    rc, new, _ = run(["git", "ls-files", "--others", "--exclude-standard", "--", "web"])
    names += [l.strip() for l in new.splitlines() if l.strip()]
    # git prints paths from the repository root: keep the part under lean/
    return sorted({n.split("lean/", 1)[-1] for n in names if n.endswith(".lean") and (ROOT / n.split("lean/", 1)[-1]).exists()})


def main():
    ap = argparse.ArgumentParser(description="the checks of one revision of the Lean side")
    ap.add_argument("--base", default="HEAD", help="the revision the web copies are compared with (default HEAD)")
    ap.add_argument("--web", nargs="*", help="compile these web copies, whatever git says")
    ap.add_argument("--no-web", action="store_true", help="steps 1 to 3 only")
    ap.add_argument("--all-web", action="store_true", help="compile web/FrcCore.lean too")
    a = ap.parse_args()
    lake, lean, rep = tool("lake"), tool("lean"), Report()

    # 1. build
    ok = rep.check("build: FrcMathlib FrcCore FrcBridge", [lake, "build", "FrcMathlib", "FrcCore", "FrcBridge"])
    certs = certificates()
    ok = rep.check(f"build: {len(certs)} certificates", [lake, "build"] + certs) and ok

    # 2. axioms
    if ok:
        rep.check("axioms: check_axioms.py", [lake, "env", sys.executable, "check_axioms.py"])
        rep.check("axioms: check_core_axioms.py", [lake, "env", sys.executable, "check_core_axioms.py"])
        for f in AXIOM_FILES:
            rc, _, _ = run(["git", "diff", "--quiet", "--", f])
            if rc != 0:
                rep.add("CHANGED", f"axioms: {f} differs from the committed file")
    else:
        rep.add("NOT RUN", "axioms: the build failed")

    # 3. generated files
    for g in GENERATORS:
        rep.check("generated: " + " ".join(g[:1] + g[-1:]), [sys.executable] + g, fails_on_output="stale")

    # 4. web copies
    if a.no_web:
        rep.add("NOT RUN", "web: --no-web")
    else:
        copies = sorted(a.web) if a.web is not None else changed_web(a.base)
        if not copies:
            rep.add("PASS", f"web: no copy differs from {a.base}")
        for c in copies:
            if c in HEAVY and not a.all_web:
                rep.add("NOT RUN", f"web: {c} (the whole core: the continuous integration compiles it)")
            elif c.startswith("web/core/") or c in HEAVY:
                rep.check(f"web: {c} (bare lean)", [lean, c])
            else:
                rep.check(f"web: {c}", [lake, "env", lean, c])

    n = {v: rep.rows.count(v) for v in ("PASS", "FAIL", "CHANGED", "NOT RUN")}
    print(f"verify: {n['PASS']} passed, {n['FAIL']} failed, {n['CHANGED']} generated file(s) changed, {n['NOT RUN']} not run")
    sys.exit(1 if n["FAIL"] else 0)


if __name__ == "__main__":
    main()
