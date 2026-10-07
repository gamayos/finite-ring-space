#!/usr/bin/env python3
"""The framework's gates G09, G10, G12, G13, G14, G15 and G19 (ledger migration, tasks LM14, LM20, LM21, LM33 and LM34,
5–7 October 2026).

    python3 ci/gates.py [all|g09|g10|g12|g13|g14|g15|g19] [--root=PATH] [--release=PAPER]

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
     ledger file under frc/ledgers/ (a paper's) or frc/ledgers/master/ (a master block's, from LM22) with the table
     ci/make_ledgers.py generates; its notebook's code cells are one per
     predicate with a python check, each with the predicate's key as its id (and the closing run-all cell).
G14  bridge coverage (task LM34): every counterpart pair that differs and has core proofs on both sides has an entry in
     lean/FrcBridge/coverage.json. A pair is a master row bound to a core key (a block file's LEAN table) and a paper row
     that names it in its ledger's master links (docs/<paper>/<paper>-ledger.json), whose Lean cells cite FrcCore; import
     rows, open master rows and pairs that share one key are not pairs. A bridged entry names a namespace of FrcBridge
     with from_master and from_paper (from_<paper><label> when several papers share it); a shared-theorem entry names core theorems that exist; a definition entry's paper row
     is a D row. A missing pair fails. A pair that waits for its paper's migration is reported while the paper is in
     revision and fails at its release (--release=PAPER).
G15  every published paper pins a release and runs green against it (task LM33; decision Q06): in the latest manifest
     releases/frc-*.json, every posted paper with a validation package is pinned, to a release whose manifest exists; the
     pinned package's checks at the tag passed (the manifest's record, written by ci/release.py serve); the site serves the
     release (docs/releases/<release>/: the archive, the web copies, each pinned sdist with its recorded SHA-256). Where git
     holds the tag, the package's tree at the tag is the one pinned. A package changed since its pin is reported: the paper
     is in revision and pins anew at its milestone.
G19  no core statement asserts unboundedness: no theorem of FrcCore states a quantity above every bound (an existential
     bounded below by a variable and above by nothing, or an existential over ℕ with no upper bound in its scope and no
     equation fixing it from bounded data; the audit's M11), and none names Infinite, Set.Infinite, Filter.atTop or
     Tendsto.

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
            for p in sorted(d.rglob("*.lean")) if d.exists() else []:            # Ledgers/Master/<Theme>.lean: a master block's certificate (LM22)
                if "_to_delete" in p.parts: continue
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
    """The migrated ledgers: the ledger files that carry the table ci/make_ledgers.py generates, the papers' (p*.py) and
    the master's blocks' (master/*.py, task LM22)."""
    d = ROOT / "frc" / "ledgers"
    if not d.exists(): return []
    files = sorted(d.glob("p*.py")) + sorted(p for p in (d / "master").glob("*.py") if p.name != "__init__.py")
    return [p for p in files if GENERATED in p.read_text(encoding="utf-8")]

def modname(f):
    return "frc.ledgers." + ("master." if f.parent.name == "master" else "") + f.stem

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
        sys.modules.pop(modname(f), None)
        L = importlib.import_module(modname(f))
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
        sys.modules.pop(modname(f), None)
        L = importlib.import_module(modname(f))
        want = sorted(L.KEYS[lab.split(":")[1]] for lab in L.R.predicates if lab.split(":")[0] == L.R.paper and lab.split(":")[1] in L.KEYS)
        got = sorted(c["id"] for c in nb["cells"] if c["cell_type"] == "code" and c["id"] != "run-all")
        if got != want: fail("G13", f"{rel}: the code cells {got} are not the keys {want}")
        bad = ML.execute(nb, ROOT)
        if bad: fail("G13", f"{rel}: cells failed: {', '.join(bad)}")
        n += 1
    return n


# ---- G14 ------------------------------------------------------------------------------------------------------------
def bridge_pairs():
    """The counterpart pairs that differ and have core proofs on both sides: (master label, "<paper>:<label>", tag)."""
    import json
    docs = ROOT / "docs"
    master = {r["label"]: r for r in json.loads((docs / "00-ledger.json").read_text(encoding="utf-8"))["rows"]}
    core = {}
    for f in sorted((ROOT / "frc" / "ledgers" / "master").glob("*.py")):
        m = re.search(r"^LEAN = (\{.*?\})", f.read_text(encoding="utf-8"), re.M)
        if m: core.update({k: f.stem for k, v in ast.literal_eval(m.group(1)).items() if v == "core"})
    out = []
    for f in sorted(docs.glob("*/*-ledger.json")):
        d = json.loads(f.read_text(encoding="utf-8"))
        rows = {r["label"]: r for b in d["blocks"] for r in b["rows"]}
        num = d["paper"].split("-")[0]
        for lab, ms in d.get("master", {}).items():
            r, cells = rows.get(lab), d.get("lean", {}).get(lab, [])
            for m in ms:
                if m not in core or r is None or r["tag"] == "I" or master[m]["tag"] == "O": continue
                if any(c["name"].rsplit(".", 1)[-1] == master[m]["key"] for c in cells): continue      # one key: no pair
                if any(c["module"].startswith("FrcCore") for c in cells): out.append((m, f"{num}:{lab}", r["tag"]))
    return out

def lean_namespaces(lib):
    """namespace -> the text between its namespace line and its end line, for every file of a Lean library; a nested
    namespace is keyed by its full name (FRC.Bridge.C1_2D1)."""
    out = {}
    for p in sorted((ROOT / "lean" / lib).rglob("*.lean")):
        body, stack = strip_lean(p.read_text(encoding="utf-8")), []
        for m in re.finditer(r"^(namespace|end) (\S+)\s*$", body, re.M):
            if m.group(1) == "namespace": stack.append((m.group(2), m.end()))
            elif stack and stack[-1][0] == m.group(2):
                name, start = stack.pop()
                out[".".join([s for s, _ in stack] + [name])] = body[start:m.start()]
    return out

def g14(release=None):
    import json
    cov_path = ROOT / "lean" / "FrcBridge" / "coverage.json"
    if not (ROOT / "docs" / "00-ledger.json").exists(): report("G14", "no docs/00-ledger.json in this tree: the pairs are not computed"); return 0
    if not cov_path.exists(): fail("G14", "lean/FrcBridge/coverage.json is missing"); return 0
    cov = json.loads(cov_path.read_text(encoding="utf-8"))
    entries = {(e["master"], e["paper"]): e for e in cov["pairs"]}
    pairs = bridge_pairs()
    ns = lean_namespaces("FrcBridge")
    core_text = "\n".join(strip_lean(p.read_text(encoding="utf-8")) for p in sorted((ROOT / "lean" / "FrcCore").rglob("*.lean")))
    tags = {(m, p): t for m, p, t in pairs}
    for key in sorted(set(tags) - set(entries)):
        fail("G14", f"00:{key[0]} with {key[1]}: a pair with core proofs on both sides and no entry in coverage.json")
    for key, e in sorted(entries.items()):
        where = f"00:{key[0]} with {key[1]}"
        st, lean = e["status"], e.get("lean")
        if st not in cov["statuses"]: fail("G14", f"{where}: unknown status {st!r}"); continue
        if st == "bridged":
            body = ns.get(lean) if lean else None
            if body is None: fail("G14", f"{where}: no namespace {lean} in lean/FrcBridge"); continue
            if not re.search(r"^theorem from_master\b", body, re.M): fail("G14", f"{where}: {lean} has no theorem from_master")
            side = "from_" + key[1].replace(":", "")                        # a bridge shared by several papers: from_2D6
            if not re.search(rf"^theorem (?:from_paper|{side})\b", body, re.M): fail("G14", f"{where}: {lean} has no theorem from_paper or {side}")
        elif st == "shared theorem":
            for name in (lean or "").split(", "):
                if not re.search(rf"^(?:theorem|lemma) {re.escape(name.rsplit('.', 1)[-1])}\b", core_text, re.M):
                    fail("G14", f"{where}: the shared theorem {name} is not in FrcCore")
        elif st == "definition":
            if key in tags and "D" not in tags[key].split("|"): fail("G14", f"{where}: the paper row is {tags[key]}, not a definition")
        elif st == "waits":
            if release and key[1].split(":")[0] == release.split("-")[0]: fail("G14", f"{where}: waits at the release of {release}")
            else: report("G14", f"{where}: waits for the paper's migration ({e['note'][:80]})")
        if key not in tags and st != "bridged": fail("G14", f"{where}: an entry that is no longer a pair (status {st})")
    return len(pairs)


# ---- G15 ------------------------------------------------------------------------------------------------------------
def g15():
    import hashlib, json, subprocess
    mans = {m.stem: json.loads(m.read_text(encoding="utf-8")) for m in sorted((ROOT / "releases").glob("frc-*.json"))} if (ROOT / "releases").is_dir() else {}
    if not mans:
        if (ROOT / "releases").is_dir(): fail("G15", "releases/ holds no manifest")
        else: report("G15", "no releases/ in this tree: the pins are not checked")
        return 0
    latest = mans[sorted(mans)[-1]]
    def at_tag(tag, path):
        r = subprocess.run(["git", "-C", str(ROOT), "rev-parse", f"{tag}:{path}"], capture_output=True, text=True, env={"GIT_OPTIONAL_LOCKS": "0", "PATH": "/usr/bin:/bin:/usr/local/bin"})
        return r.stdout.strip() if r.returncode == 0 else None
    n = 0
    for p in latest["papers"]:
        if not (p.get("posted") and p.get("package")): continue
        n += 1; key = p["key"]
        if not p.get("pinned"): fail("G15", f"{key}: a posted paper with a package and no pinned release"); continue
        rel = p.get("pinned_release", latest["release"])
        man = mans.get(rel)
        if man is None: fail("G15", f"{key}: pinned to {rel}, which has no manifest"); continue
        pin = next((q for q in man["papers"] if q["key"] == key), None)
        if pin is None or not pin.get("pinned"): fail("G15", f"{key}: {rel} does not pin it"); continue
        res = pin.get("results")
        if "results" not in pin: fail("G15", f"{key}: {rel} is not served (run ci/release.py serve {rel})")
        elif res is None: report("G15", f"{key}: {p['package']} keeps no check records (results.json) at {rel}; it gains them when the paper migrates (LM36)")
        elif res[0] != res[1]: fail("G15", f"{key}: {p['package']} at {rel} passes {res[0]} of {res[1]} checks")
        out = ROOT / "docs" / "releases" / rel
        if not (out / f"{rel}.tar.gz").exists() or not (out / "lean" / "web").is_dir(): fail("G15", f"{key}: the site does not serve {rel} (docs/releases/{rel}/)")
        if pin.get("sdist"):
            f = out / "pkg" / pin["sdist"]
            if not f.exists(): fail("G15", f"{key}: the pinned sdist {pin['sdist']} is not served under docs/releases/{rel}/pkg/")
            elif hashlib.sha256(f.read_bytes()).hexdigest() != pin["sdist_sha256"]: fail("G15", f"{key}: the served {pin['sdist']} differs from the pin")
        tree = at_tag(man["tag"], p["package"])
        if tree is None: report("G15", f"{key}: the tag {man['tag']} is not in this clone; the package tree is not rechecked")
        elif tree != pin.get("package_tree"): fail("G15", f"{key}: {p['package']} at {man['tag']} is not the pinned tree")
        head = at_tag("HEAD", p["package"])
        if tree and head and head != tree: report("G15", f"{key}: {p['package']} changed since {rel} (in revision; it pins anew at its milestone)")
    return n


# ---- G19 ------------------------------------------------------------------------------------------------------------
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|noncomputable\s+)*(theorem|lemma)\s+([^\s:(\[{]+)", re.M)
NAMES = re.compile(r"\bInfinite\b|Set\.Infinite|Filter\.atTop|\batTop\b|\bTendsto\b|¬\s*Finite\b")

def _scope(stmt, start):
    """The text a binder scopes over: from `start` to the closing bracket that ends it."""
    depth, s = 0, stmt[start:]
    for k, ch in enumerate(s):
        depth += ch in "([{⟨"; depth -= ch in ")]}⟩"
        if depth < 0: return s[:k]
    return s


def _determined(V, s):
    """An equation in the scope that fixes the variable from bounded data: one side free of it, the other holding it
    outside any remainder (`κ = 2 * m`, `t = a * q`, `x = p * q + r`), so the witness is at most that side."""
    for eq in re.finditer(r"([^=∧∨↔→,]+?)\s=\s([^=∧∨↔→,]+)", s):
        a, b = eq.group(1), eq.group(2)
        ina, inb = re.search(rf"(?<![\w'.]){V}(?![\w'])", a), re.search(rf"(?<![\w'.]){V}(?![\w'])", b)
        side = b if (inb and not ina) else a if (ina and not inb) else None
        if side and not re.search(rf"%\s*\(?[^,]*?(?<![\w'.]){V}(?![\w'])|(?<![\w'.]){V}(?![\w'])[^,=]*?\)?\s*%", side): return True
    return False


def unbounded(stmt):
    """An existential that can exceed every bound (gate G19; the audit's M11, 7 October 2026). Two cases fail:
    a variable bounded below by a variable and above by nothing; and a variable over ℕ — annotated `Nat`/`ℕ`, or used as
    an exponent, under a remainder or in an order relation — with no upper bound in its scope and no equation that fixes
    it from bounded data. An existential over the residues of a shell is bounded by its type."""
    for q in re.finditer(r"∃\s*([^,]+?),", stmt):
        binder = q.group(1)
        names = [v for v in re.split(r"[\s()]+", binder.split(":")[0]) if v and v != "_"]
        typ = binder.split(":", 1)[1].strip() if ":" in binder else ""
        s = _scope(stmt, q.end())
        for v in names:
            V = re.escape(v)
            lower = re.search(rf"(?<![\w'.]){V}(?![\w'])\s*(?:>|≥)\s*[A-Za-z_]|[A-Za-z_][\w']*\s*(?:<|≤)\s*{V}(?![\w'])", s)
            upper = re.search(rf"(?<![\w'.]){V}(?![\w'])\s*(?:<|≤)|(?:>|≥)\s*{V}(?![\w'])", s)
            if lower and not upper: return f"∃ {v}, bounded below by a variable and above by nothing"
            if upper or re.search(rf"(?<![\w'.]){V}(?![\w'])\s*∣", s): continue           # bounded, or a divisor
            nat = typ in ("Nat", "ℕ") or (not typ and re.search(
                rf"\^\s*\(?{V}(?![\w'])|(?<![\w'.]){V}(?![\w'])\)?\s*%|%\s*\(?{V}(?![\w'])|(?<![\w'.]){V}(?![\w'])\s*(?:<|≤|>|≥|∣)|(?:<|≤|>|≥|∣)\s*{V}(?![\w'])", s))
            if nat and not _determined(V, s): return f"∃ {v} over ℕ with no upper bound in its scope"
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
    n14 = g14(next((a.split("=", 1)[1] for a in sys.argv[1:] if a.startswith("--release=")), None)) if which in ("all", "g14") else 0
    n15 = g15() if which in ("all", "g15") else 0
    n19 = g19(fw) if which in ("all", "g19") else 0
    for r in REPORTS: print(r)
    for f in FAILS: print("FAIL", f)
    print(f"gates {which}: {len(fw)} framework files; {n12} migrated ledger(s) checked (G12); {n13} notebook(s) executed (G13); {n14} bridge pair(s) covered (G14); {n15} pinned paper(s) (G15); {n19} core theorems scanned (G19); {len(REPORTS)} report(s); "
          + ("green" if not FAILS else f"{len(FAILS)} failure(s)"))
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
