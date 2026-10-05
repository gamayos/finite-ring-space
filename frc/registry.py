"""frc.registry — the registry of checks, once for every ledger (base tier; ledger migration, task LM15, 5 October 2026).

It replaces the copies that every validation package carries (`check` in 21 packages, `summary` in 19, `predicate`,
`verify_all`, `markers` and `_run_block` in 12). A package moves to it when its paper migrates (task LM36); until then
the package keeps its own copy, pinned in its release.

One Registry per ledger file:

    R = Registry("25", "godel", ledger={"A1": "25:C1", "A2": "25:C2, 25:C3"})
    @R.block("A", "Gödel's hypotheses over a finite structure")
    def block_A():
        # 25:C1 (p25010)
        R.check("A1", "no finite structure interprets Q", ok, "detail")
    R.verify_all()                  # every block once, the census, the verdict
    R.predicate("25:C1")            # one predicate: the blocks that cite it, its marker, its records
    R.summary(write=True)           # results.json, the records the site reads

A record is {"id", "rows", "block", "script", "label", "ok", "detail", "kind"}, the schema of today's results.json.
A marker is a comment line `# <paper>:<label> (<key>)` on the check that decides the predicate; several may share it.
"""
import json, os, re

KINDS = ("EXACT", "CHART", "APPROX", "MIXED", "PROFINITE")
_ALIAS = {"[approx]": "APPROX", "[chart]": "CHART", "EXACT+CHART": "MIXED"}
MARKER = re.compile(r"\s*# ((?:\d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)(?:, \d+:[A-Z]+\d+[a-z]?(?: \(p\d{5}\))?)*)\s*$")


class Registry:
    def __init__(self, paper, script, ledger, predicates=None, sources=()):
        """paper: the ledger's number ("25", "00"); script: the name results.json and the pages carry; ledger: check id ->
        the predicates it decides or corroborates ("25:C2, 25:C3"); predicates: predicate -> its deciding check id (by
        default the first check that lists it first, else the first check that cites it); sources: the files whose markers
        locate the checks."""
        self.paper, self.script, self.ledger = str(paper), script, dict(ledger)
        self.results, self.blocks, self._ran = [], {}, set()
        self.sources = list(sources)
        if predicates is None:
            predicates = {}
            for pid, rows in self.ledger.items():                           # a check decides the predicate it lists first
                labs = _split(rows)
                if labs: predicates.setdefault(labs[0], pid)
            for pid, rows in self.ledger.items():                           # and corroborates the others
                for lab in _split(rows): predicates.setdefault(lab, pid)
        self.predicates = dict(predicates)
        for lab, pid in self.predicates.items():
            if pid not in self.ledger: raise ValueError(f"{lab}: its deciding check {pid} is not in the ledger")

    # -- recording -------------------------------------------------------------------------------------------------------
    def check(self, pid, label, ok, detail="", kind="EXACT"):
        """Record one check; pid must be in the ledger. Returns ok."""
        if pid not in self.ledger: raise KeyError(f"{pid}: no such check in the ledger of {self.script}")
        kind = _ALIAS.get(kind, kind)
        if kind not in KINDS: raise ValueError(f"{pid}: kind {kind!r} is not one of {KINDS}")
        ok = bool(ok)
        rec = {"id": pid, "rows": self.ledger[pid], "block": pid[0], "script": self.script, "label": label, "ok": ok,
               "detail": str(detail), "kind": kind}
        self.results.append(rec)
        print(f"  [{'PASS' if ok else 'FAIL'}] {pid:4s} {kind:9s} [{rec['rows']}] {label}" + (f"  --  {detail}" if detail else ""))
        return ok

    # -- blocks ----------------------------------------------------------------------------------------------------------
    def block(self, letter, title=""):
        """Decorator: register the function as block `letter` (its checks have ids starting with the letter)."""
        def deco(fn):
            self.blocks[letter] = (title, fn)
            return fn
        return deco

    def run_block(self, letter):
        """Run a block once per session."""
        if letter not in self._ran:
            self.blocks[letter][1](); self._ran.add(letter)

    # -- verdicts ----------------------------------------------------------------------------------------------------------
    def summary(self, write=True, expect=None, path="results.json"):
        """Print the verdict; write results.json if asked. A check of `expect` that never reported fails the census."""
        n_ok = sum(r["ok"] for r in self.results)
        ran = sorted({r["id"] for r in self.results})
        census = expect is None or ran == sorted(expect)
        print(f"\nSUMMARY: {n_ok}/{len(self.results)} checks passed" + ("" if n_ok == len(self.results) else "  <-- FAILURES"))
        if not census: print(f"  <-- CENSUS: expected {sorted(expect)}, ran {ran}")
        if write:
            with open(path, "w", encoding="utf-8") as f: json.dump(self.results, f, indent=1, ensure_ascii=False)
        return n_ok == len(self.results) and census

    def verify_all(self):
        """Every block once, then the summary with the census over the whole ledger. True iff every check passed."""
        for b in sorted(self.blocks): self.run_block(b)
        return self.summary(write=False, expect=list(self.ledger))

    # -- predicates --------------------------------------------------------------------------------------------------------
    def markers(self):
        """predicate label -> (file name, line) of the first marker that names it, over the registry's sources."""
        out = {}
        for src in self.sources:
            with open(src, encoding="utf-8") as fh:
                for i, line in enumerate(fh, 1):
                    m = MARKER.match(line)
                    if m:
                        for lab in re.findall(r"\d+:[A-Z]+\d+[a-z]?", m.group(1)): out.setdefault(lab, (os.path.basename(src), i))
        return out

    def predicate(self, label, lines=14):
        """Verify one predicate: run the deciding block and every block whose checks cite it, print the deciding check's
        source from its marker and every record that cites the predicate. True iff the deciding check reported and every
        citing record passed; None when the ledger has no python witness for it."""
        pid = self.predicates.get(label)
        if pid is None:
            print(f"{label}: no python witness (see the predicate's Lean witness or its source)"); return None
        citing = {i[0] for i, rows in self.ledger.items() if label in _split(rows)}
        for b in sorted({pid[0]} | citing): self.run_block(b)
        mk = self.markers().get(label)
        if mk:
            src = next(s for s in self.sources if os.path.basename(s) == mk[0])
            text = open(src, encoding="utf-8").read().split("\n")
            print(f"— {mk[0]}:{mk[1]} (the check that decides {label}: {pid})")
            for j in range(mk[1] - 1, min(mk[1] - 1 + lines, len(text))):
                if not text[j].strip(): break
                print(f"{j + 1:5d}  {text[j]}")
        recs = [r for r in self.results if label in _split(r["rows"])]
        ok = all(r["ok"] for r in recs) and any(r["id"] == pid for r in recs)
        for r in recs:
            role = "(deciding)" if r["id"] == pid else "(corroborating)"
            print(f"  [{'PASS' if r['ok'] else 'FAIL'}] {r['id']:4s} {role:16s} {r['detail'][:150]}")
        print(f"{label}: {'VERIFIED' if ok else 'FAILED'} — {len(recs)} record(s)")
        return ok


def _split(rows):
    return [t.strip() for t in rows.split(",") if t.strip()]
