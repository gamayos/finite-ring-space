"""7-spacetime's ledger file (frc/ledgers/p07_spacetime.py): the ledger file green, its markers on its deciding checks
with the keys of the generated table (the carried rows under their origin keys), every witnessed predicate decided by a
check that cites it, every block exact (no chart), and the programme's three laboratory pairs (the Subjects 13, 173,
1549 in the Carriers 233, 30089, 2408561; the enumerations on 13 alone)."""
import io
import json
import re
import unittest
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
_RUN = {}


def ledger():
    """The ledger file, run once per session."""
    from frc.ledgers import p07_spacetime as L
    if "ok" not in _RUN:
        with redirect_stdout(io.StringIO()):
            _RUN["ok"] = L.R.verify_all()
    return L


class LedgerTest(unittest.TestCase):
    def test_ledger_file(self):
        L = ledger()
        self.assertTrue(_RUN["ok"])
        marks = L.R.markers()
        for lab in L.R.predicates: self.assertIn(lab, marks)
        self.assertEqual(L.PAPER, "7-spacetime")
        for lab, pid in L.PREDICATES.items():
            self.assertIn(lab, [x.strip() for x in L.LEDGER[pid].split(",")])
        for lab in L.LEAN:
            self.assertTrue(f"7:{lab}" in L.PREDICATES or lab in L.LEAN_ONLY, lab)
        self.assertEqual(L.LEAN_ONLY, ())
        self.assertEqual(set(L.BLOCK), {"A", "B", "C", "D", "F", "P"})
        kinds = {b: {r["kind"] for r in L.R.results if r["id"][0] == b} for b in L.BLOCK}
        for b in L.BLOCK: self.assertEqual(kinds[b], {"EXACT"}, b)
        self.assertEqual(L.SHELLS, [(13, 2), (173, 2), (1549, 2)])
        self.assertEqual(L.PAIRS, [(13, 233), (173, 30089), (1549, 2408561)])
        self.assertEqual((L.MID, L.ENUM), (L.SHELLS[:2], L.SHELLS[:1]))
        self.assertEqual((L.P, L.G, L.OM), (13, 2, 233))

    def test_markers_carry_the_keys(self):
        from frc.ledgers import p07_spacetime as L
        data = json.loads((ROOT / "docs" / "7-spacetime" / "7-spacetime-ledger.json").read_text(encoding="utf-8"))
        keys = {r["label"]: r["key"] for b in data["blocks"] for r in b["rows"]}
        text = Path(L.__file__).read_text(encoding="utf-8")
        found = 0
        for line in text.splitlines():
            if re.match(r"\s*# 7:[A-Z]+\d+ \(p\d{5}\)", line):              # a carried row keeps its origin key (p00021, p03008, p21018, p38050)
                for lab, key in re.findall(r"7:([A-Z]+\d+) \((p\d{5})\)", line):
                    self.assertEqual(keys[lab], key); found += 1
                    if L.KEYS: self.assertEqual(L.KEYS[lab], key)
        self.assertEqual(found, len(L.PREDICATES))

    def test_rows_cited_exist(self):
        from frc.ledgers import p07_spacetime as L
        data = json.loads((ROOT / "docs" / "7-spacetime" / "7-spacetime-ledger.json").read_text(encoding="utf-8"))
        labels = {r["label"] for b in data["blocks"] for r in b["rows"]}
        for pid, rows in L.LEDGER.items():
            for lab in rows.split(","):
                self.assertIn(lab.strip().split(":")[1], labels, pid)
        witnessed = {r["label"] for b in data["blocks"] for r in b["rows"] if r.get("tag") == "T"}
        self.assertEqual(witnessed, {lab.split(":")[1] for lab in L.PREDICATES})         # every T row has a deciding check

    def test_lean_table(self):
        from frc.ledgers import p07_spacetime as L
        self.assertEqual(L.LEAN["D5"], "ml")                                              # Chevalley–Warning, on Mathlib alone
        self.assertEqual(L.LEAN["A31"], "core, ml")                                       # the floor: the identity in the core, the number on Mathlib
        self.assertEqual({v for k, v in L.LEAN.items() if k not in ("D5", "A31")}, {"core"})
        self.assertEqual(len(L.LEAN), 51)                                                 # A31, A32, A33 since 6 November 2026


if __name__ == "__main__":
    unittest.main()
