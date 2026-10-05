#!/usr/bin/env python3
"""The framework's gates G09, G10, G12, G13 and G19 (ledger migration, tasks LM14, LM20 and LM21, 5 October 2026).

    python3 ci/gates.py [all|g09|g10|g12|g13|g19] [--root PATH]

G09  imports follow the layers of the theme map (frc/themes.py): a file imports only files of lower rank, or the files
     listed before it in its own theme; a ledger file imports themes; nothing imports a ledger file. The exact tiers have
     no float and no third-party import; in Lean, the core has no Float and a Mathlib theme file outside the chart has
     no reals. A paper module of today (LEGACY) imports themes, key files and its own paper's modules only (gated since LM18).
G10  size budgets (decision Q03), on framework files and migrated ledgers only: a python file 1,800 lines, a core file
     800, a Mathlib file 1,800, and a file with its import closure 3,500.
G12  every keyed declaration of a migrated ledger has a python marker and a notebook cell, or is declared Lean-only
     (task LM21): each row of the ledger file's table LEAN has its predicate in the registry's PREDICATES, a marker on
     the deciding check and a notebook cell with its key as id, unless LEAN_ONLY lists it; and the parts that
     ci/make_ledgers.py generates (the table, the notebook's cells, the certificates) are current.
G13  every migrated ledger's notebook executes green, with cell ids equal to keys (task LM20): a migrated ledger is a
     ledger file under frc/ledgers/ with the table ci/make_ledgers.py generates; its notebook's code cells are one per
     predicate with a python check, each with the predicate's key as its id (and the closing run-all cell).
G19  no core statement asserts unboundedness: no theorem of FrcCore states a quantity above every bound (an existential
     bounded below by a variable and above by nothing), and none names Infinite, Set.Infinite, Filter.atTop or Tendsto.

Exit 1 when a gated check fails. Standard library only.
"""
import ast, re, sys
from pathlib import Path

ROOT = Path(next((a.split("=", 1)[1] for a in sys.argv[1:] if a.startswith("--root=")), Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(ROOT))
from frc import themes as TM                                    # noqa: E402

FAILS, REPORTS = [], []


def fail(gate, msg): FAILS.append(f"{gate}: {msg}")
def report(gate, msg): REPORTS.append(f"{gate} (report): {msg}")


# ---- the map: every framework file with its theme, rank and place in its theme ---------------------------------------
def framework(planned=False):
    """path -> (kind, theme, rank, index, exact) for the theme files (those that exist, or every file of the map when
    planned), the keys and the ledger files."""
    out = {}
    for kind in ("py", "core", "ml"):
        for f, theme, rank, i in TM.files(kind):
            if planned or (ROOT / f).exists(): out[f] = (kind, theme, rank, i, TM.THEMES[theme]["exact"])
    for p in (ROOT / "frc" / "ledgers").rglob("*.py") if (ROOT / "frc" / "ledgers").exists() else []:
        if p.name != "__init__.py": out[str(p.relative_to(ROOT))] = ("py", "ledgers", TM.LEDGERS["rank"], 0, True)
    for lib, kind in (("FrcCore", "core"), ("FrcLedger", "ml")):
        for sub, key in (("Keys", "keys"), ("Ledgers", "ledgers")):
            d = ROOT / "lean" / lib / sub
            for p in sorted(d.glob("*.lean")) if d.exists() else []:
                out[str(p.relative_to(ROOT))] = (kind, key, (TM.KEYS if key == "keys" else TM.LEDGERS)["rank"], 0, True)
    return out


def strip_lean(text):
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def lean_imports(path):
    return re.findall(r"^import\s+(\S+)", (ROOT / path).read_text(encoding="utf-8"), re.M)


def lean_path(mod):
    """FrcCore.Theme.Fourier -> lean/FrcCore/Theme/Fourier.lean (None for Init, Mathlib and the like)."""
    if not mod.startswith(("FrcCore", "FrcLedger")): return None
    return "lean/" + mod.replace(".", "/") + ".lean"


def py_imports(path):
    """The frc modules a python file imports, as paths, and the top-level non-frc modules."""
    tree = ast.parse((ROOT / path).read_text(encoding="utf-8"))
    pkg = Path(path).parent
    frc, other = [], []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                (frc if a.name.split(".")[0] == "frc" else other).append(a.name)
        elif isinstance(node, ast.ImportFrom):
            if node.level:                                                   # a relative import inside frc/
                base = pkg
                for _ in range(node.level - 1): base = base.parent
                mod = (str(base).replace("/", ".") + ("." + node.module if node.module else ""))
                if node.module: frc.append(mod)
                else: frc += [mod + "." + a.name for a in node.names]
            elif node.module and node.module.split(".")[0] == "frc":
                frc.append(node.module)
                frc += [node.module + "." + a.name for a in node.names]
            elif node.module:
                other.append(node.module)
    paths = []
    for m in frc:
        p = m.replace(".", "/")
        if (ROOT / p).is_dir(): paths.append(p + "/__init__.py")
        elif p != "frc": paths.append(p + ".py")                           # a planned theme is judged by the map
    return sorted(set(paths)), sorted({o.split(".")[0] for o in other})


def allowed(src, dst, fw):
    """May framework file src import framework file dst? (dst judged against the whole map, planned files included)"""
    s, d = fw[src], PLANNED.get(dst)
    if d is None and dst.startswith("frc/ledgers/"): d = ("py", "ledgers", TM.LEDGERS["rank"], 0, True)
    if d is None: return True                                              # not a framework file: judged elsewhere
    if d[1] == "ledgers": return False                                     # nothing imports a ledger file
    if s[1] == "ledgers": return d[1] != "ledgers"                         # a ledger file imports themes (and keys)
    if s[1] == "keys": return d[1] not in ("keys", "ledgers")
    if d[2] < s[2]: return True
    return d[1] == s[1] and d[3] < s[3]                                    # an earlier file of the same theme


# ---- G09 ------------------------------------------------------------------------------------------------------------
FLOAT_CALLS = {"float", "complex"}

def g09(fw):
    for f, (kind, theme, rank, i, exact) in sorted(fw.items()):
        if kind == "py":
            deps, other = py_imports(f)
            for d in deps:
                if d.endswith("__init__.py") or d == "frc/themes.py": continue
                if not allowed(f, d, fw): fail("G09", f"{f} ({theme}, rank {rank}) imports {d}")
            if exact:
                for o in other:
                    if o not in TM.EXACT_STDLIB: fail("G09", f"{f}: import of {o} in an exact tier")
                tree = ast.parse((ROOT / f).read_text(encoding="utf-8"))
                for node in ast.walk(tree):
                    if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
                        fail("G09", f"{f}:{node.lineno}: a float literal in an exact tier")
                    elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in FLOAT_CALLS:
                        fail("G09", f"{f}:{node.lineno}: {node.func.id}() in an exact tier")
                    elif isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "math" and node.attr not in TM.MATH_EXACT:
                        fail("G09", f"{f}:{node.lineno}: math.{node.attr} in an exact tier")
                    elif isinstance(node, ast.ImportFrom) and node.module == "math":
                        for a in node.names:
                            if a.name not in TM.MATH_EXACT: fail("G09", f"{f}:{node.lineno}: from math import {a.name} in an exact tier")
        else:
            for m in lean_imports(f):
                d = lean_path(m)
                if kind == "core" and not (m.startswith("FrcCore") or m.startswith("Init")):
                    fail("G09", f"{f}: the core imports {m}")
                if d and not allowed(f, d, fw): fail("G09", f"{f} ({theme}, rank {rank}) imports {m}")
                if d and d in TM.LEGACY: fail("G09", f"{f} imports the paper module {m}")
            body = strip_lean((ROOT / f).read_text(encoding="utf-8"))
            if kind == "core" and re.search(r"\bFloat\b", body): fail("G09", f"{f}: Float in the core")
            if kind == "ml" and theme not in ("chart", "keys", "ledgers") and re.search(r"ℝ|\bReal\b|\bFloat\b|ℂ", body):
                fail("G09", f"{f}: the reals in an exact Mathlib theme")
    # a framework file the map does not place
    for q in sorted((ROOT / "frc").glob("*.py")):
        r = str(q.relative_to(ROOT))
        if r not in PLANNED and q.name not in ("__init__.py", "themes.py"): fail("G09", f"{r}: not in the theme map")
    for lib in ("FrcCore", "FrcLedger"):
        d = ROOT / "lean" / lib / "Theme"
        for q in sorted(d.glob("*.lean")) if d.exists() else []:
            r = str(q.relative_to(ROOT))
            if r not in PLANNED: fail("G09", f"{r}: not in the theme map")
    # the paper modules of today: a cross-paper import fails once LEGACY_IMPORTS_ENFORCED (LM18); before, it was reported
    for f, (paper, _) in sorted(TM.LEGACY.items()):
        if not (ROOT / f).exists(): continue
        for m in lean_imports(f):
            d = lean_path(m)
            if d in TM.LEGACY and TM.LEGACY[d][0] != paper:
                (fail if TM.LEGACY_IMPORTS_ENFORCED else report)("G09", f"{f} ({paper}) imports {m} ({TM.LEGACY[d][0]})")


# ---- G10 ------------------------------------------------------------------------------------------------------------
def nlines(f): return (ROOT / f).read_text(encoding="utf-8").count("\n")

def closure(f, fw):
    seen, todo = set(), [f]
    while todo:
        x = todo.pop()
        if x in seen: continue
        seen.add(x)
        if x.endswith(".py"): todo += [d for d in py_imports(x)[0] if (ROOT / d).exists()]
        else: todo += [p for p in (lean_path(m) for m in lean_imports(x)) if p and (ROOT / p).exists()]
    return seen

def g10(fw):
    B = TM.BUDGETS
    for f, (kind, theme, *_r) in sorted(fw.items()):
        cap = {"py": B["python_file"], "core": B["core_file"], "ml": B["mathlib_file"]}[kind]
        n = nlines(f)
        if n > cap: fail("G10", f"{f}: {n} lines, over {cap}")
        c = closure(f, fw); total = sum(nlines(x) for x in c)
        if total > B["executable"]: fail("G10", f"{f}: {total} lines with its import closure ({len(c)} files), over {B['executable']}")


# ---- G13 ------------------------------------------------------------------------------------------------------------
GENERATED = "# ---- generated by ci/make_ledgers.py"

def migrated():
    """The migrated ledgers: the ledger files that carry the table ci/make_ledgers.py generates."""
    d = ROOT / "frc" / "ledgers"
    return [p for p in sorted(d.glob("p*.py")) if GENERATED in p.read_text(encoding="utf-8")] if d.exists() else []

def make_ledgers():
    import importlib.util
    spec = importlib.util.spec_from_file_location("make_ledgers", Path(__file__).resolve().parent / "make_ledgers.py")
    ML = importlib.util.module_from_spec(spec); spec.loader.exec_module(ML); ML.ROOT = ROOT      # the tree under check
    return ML

def g12():
    import importlib, json
    files = migrated()
    if not files: return 0
    if not (ROOT / "docs").is_dir() or not (ROOT / "lean" / "make_predicates.py").exists():
        fail("G12", "docs/ or lean/ is missing: the generated parts of the migrated ledgers cannot be checked"); return len(files)
    stale, _, problems = make_ledgers().run(check=True)
    for s in problems: fail("G12", s)
    for s in stale: fail("G12", f"{s}: stale (run ci/make_ledgers.py)")
    for f in files:
        sys.modules.pop(f"frc.ledgers.{f.stem}", None)
        L = importlib.import_module(f"frc.ledgers.{f.stem}")
        marks = L.R.markers(); nbp = f.with_suffix(".ipynb")
        cells = {c["id"] for c in json.loads(nbp.read_text(encoding="utf-8"))["cells"]} if nbp.exists() else set()
        for label in L.LEAN:
            lab, key = f"{L.R.paper}:{label}", L.KEYS[label]
            if label in L.LEAN_ONLY: continue
            if lab not in L.R.predicates: fail("G12", f"{f.name}: {lab} ({key}) has a Lean declaration, no python check, and is not declared Lean-only"); continue
            if lab not in marks: fail("G12", f"{f.name}: {lab} ({key}) has no marker on its deciding check {L.R.predicates[lab]}")
            if key not in cells: fail("G12", f"{nbp.name}: no cell {key} for {lab}")
        for label in L.LEAN_ONLY:
            if label not in L.LEAN: fail("G12", f"{f.name}: {label} is declared Lean-only and has no Lean declaration")
    return len(files)

def g13():
    import importlib, json
    ML = make_ledgers()
    n = 0
    for f in migrated():
        nbp = f.with_suffix(".ipynb"); rel = nbp.relative_to(ROOT)
        if not nbp.exists(): fail("G13", f"{rel}: no notebook for {f.name}"); continue
        nb = json.loads(nbp.read_text(encoding="utf-8"))
        sys.modules.pop(f"frc.ledgers.{f.stem}", None)
        L = importlib.import_module(f"frc.ledgers.{f.stem}")
        want = sorted(L.KEYS[lab.split(":")[1]] for lab in L.R.predicates if lab.split(":")[0] == L.R.paper and lab.split(":")[1] in L.KEYS)
        got = sorted(c["id"] for c in nb["cells"] if c["cell_type"] == "code" and c["id"] != "run-all")
        if got != want: fail("G13", f"{rel}: the code cells {got} are not the keys {want}")
        bad = ML.execute(nb, ROOT)
        if bad: fail("G13", f"{rel}: cells failed: {', '.join(bad)}")
        n += 1
    return n


# ---- G19 ------------------------------------------------------------------------------------------------------------
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|noncomputable\s+)*(theorem|lemma)\s+([^\s:(\[{]+)", re.M)
NAMES = re.compile(r"\bInfinite\b|Set\.Infinite|Filter\.atTop|\batTop\b|\bTendsto\b|¬\s*Finite\b")

def unbounded(stmt):
    """An existential variable bounded below by a variable and above by nothing, in the conjunct after its binder."""
    for q in re.finditer(r"∃\s*([^,]+?),", stmt):
        names = [v for v in re.split(r"[\s()]+", q.group(1).split(":")[0]) if v and v != "_"]
        depth, j, s = 0, q.end(), stmt[q.end():]
        for k, ch in enumerate(s):                                         # the scope of the binder: to the closing bracket
            depth += ch in "([{⟨"; depth -= ch in ")]}⟩"
            if depth < 0: s = s[:k]; break
        for v in names:
            V = re.escape(v)
            lower = re.search(rf"(?<![\w'.]){V}(?![\w'])\s*(?:>|≥)\s*[A-Za-z_]|[A-Za-z_][\w']*\s*(?:<|≤)\s*{V}(?![\w'])", s)
            upper = re.search(rf"(?<![\w'.]){V}(?![\w'])\s*(?:<|≤)|(?:>|≥)\s*{V}(?![\w'])", s)
            if lower and not upper: return f"∃ {v}, bounded below by a variable and above by nothing"
    return None

def g19(fw):
    core = sorted((ROOT / "lean" / "FrcCore").rglob("*.lean"))
    n = 0
    for p in core:
        body = strip_lean(p.read_text(encoding="utf-8"))
        for m in DECL.finditer(body):
            end = body.find(":=", m.end())
            stmt = " ".join(body[m.end(): end if end > 0 else len(body)].split())
            n += 1
            why = unbounded(stmt) or (f"names {NAMES.search(stmt).group(0)}" if NAMES.search(stmt) else None)
            if why: fail("G19", f"{p.relative_to(ROOT)}: {m.group(2)}: {why}")
    return n


PLANNED = {}

def main():
    which = next((a for a in sys.argv[1:] if not a.startswith("--")), "all")
    fw = framework()
    PLANNED.update(framework(planned=True)); PLANNED.update(fw)
    if which in ("all", "g09"): g09(fw)
    if which in ("all", "g10"): g10(fw)
    n12 = g12() if which in ("all", "g12") else 0
    n13 = g13() if which in ("all", "g13") else 0
    n19 = g19(fw) if which in ("all", "g19") else 0
    for r in REPORTS: print(r)
    for f in FAILS: print("FAIL", f)
    print(f"gates {which}: {len(fw)} framework files; {n12} migrated ledger(s) checked (G12); {n13} notebook(s) executed (G13); {n19} core theorems scanned (G19); {len(REPORTS)} report(s); "
          + ("green" if not FAILS else f"{len(FAILS)} failure(s)"))
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
