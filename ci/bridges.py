"""ci/bridges.py — the python side of the bridges (ledger migration, task LM34, 7 October 2026).

A bridge joins a master row and a paper row whose keys differ and share a clause. Its Lean side is a namespace of
lean/FrcBridge, which states the Clause and derives it from each side's core key; lean/FrcBridge/coverage.json lists
every pair with core proofs on both sides and its status, and gate G14 keeps the list complete. This runner checks the
python side: for each bridged pair it runs the master row's python witness from its block file, and the paper row's
witness from the paper's ledger file once the paper has migrated (LM36). Until then the paper's own validation package
checks its row, pinned in its release.

    python3 -B ci/bridges.py               every bridged pair
    python3 -B ci/bridges.py C3 8:B3       the pairs of 00:C3, or of 8:B3
    python3 -B ci/bridges.py --list        the coverage, without running

It lives in ci/ because it imports ledger files, which nothing in frc/ may do (gate G09).

Exit 1 when a witness that ran fails. Standard library only.
"""
import ast, contextlib, importlib, io, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
COVERAGE = ROOT / "lean" / "FrcBridge" / "coverage.json"
RUN = ("bridged", "shared theorem")


def coverage():
    return json.loads(COVERAGE.read_text(encoding="utf-8"))["pairs"]


def master_module(label):
    """The block file that proves a master row (its LEAN table), or None."""
    for f in sorted((ROOT / "frc" / "ledgers" / "master").glob("*.py")):
        m = re.search(r"^LEAN = (\{.*?\})", f.read_text(encoding="utf-8"), re.M)
        if m and label in ast.literal_eval(m.group(1)): return "frc.ledgers.master." + f.stem
    return None


def paper_module(num):
    """The migrated ledger file of paper `num` (frc/ledgers/p03_causality.py for 3), or None."""
    hits = sorted((ROOT / "frc" / "ledgers").glob(f"p{int(num):02d}_*.py"))
    return "frc.ledgers." + hits[0].stem if hits else None


def witness(module, label, quiet=True):
    """Run one predicate's python witness: True, False, or None when the ledger has none."""
    L = importlib.import_module(module)
    out = io.StringIO()
    with contextlib.redirect_stdout(out if quiet else sys.stdout):
        ok = L.R.predicate(label)
    return ok


def main(argv):
    pairs = coverage()
    sel = [a for a in argv if not a.startswith("--")]
    if sel: pairs = [e for e in pairs if e["master"] in sel or e["paper"] in sel]
    if "--list" in argv:
        for e in pairs: print(f"00:{e['master']:4s} {e['paper']:7s} {e['status']:17s} {e.get('lean') or ''}")
        return 0
    bad = 0
    for e in pairs:
        if e["status"] not in RUN: continue
        mm = master_module(e["master"])
        mok = witness(mm, f"00:{e['master']}") if mm else None
        num, lab = e["paper"].split(":")
        pm = paper_module(num)
        pok = witness(pm, f"{int(num)}:{lab}") if pm else "package"
        bad += (mok is False) + (pok is False)
        say = lambda v: {True: "VERIFIED", False: "FAILED", None: "no python witness", "package": "its package (until LM36)"}[v]
        print(f"00:{e['master']:4s} {say(mok):18s} | {e['paper']:7s} {say(pok):24s} | {e['lean']}")
    print(f"bridges: {sum(e['status'] in RUN for e in pairs)} pair(s) run; " + ("green" if not bad else f"{bad} failure(s)"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
