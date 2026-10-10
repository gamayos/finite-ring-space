"""21-gravity's ledger file (frc/ledgers/p21_gravity.py): the ledger file green, its markers on its deciding checks with the
keys of the generated table, every witnessed predicate decided by a check that cites it, the exact blocks float-free and
the chart blocks anchored to the scale import."""
import io
import json
import re
import unittest
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
_RUN = {}


def ledger():
    """The ledger file, run once per session (its blocks take a few seconds)."""
    from frc.ledgers import p21_gravity as L
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
        self.assertEqual(L.PAPER, "21-gravity")
        for lab, pid in L.PREDICATES.items():
            self.assertIn(lab, [x.strip() for x in L.LEDGER[pid].split(",")])
        for lab in L.LEAN:
            self.assertTrue(f"21:{lab}" in L.PREDICATES or lab in L.LEAN_ONLY, lab)
        self.assertEqual(set(L.BLOCK), {"A", "B", "C", "D", "E", "F", "G"})
        kinds = {b: {r["kind"] for r in L.R.results if r["id"][0] == b} for b in L.BLOCK}
        for b in "ABCD": self.assertEqual(kinds[b], {"EXACT"}, b)
        for b in "EFG": self.assertEqual(kinds[b], {"CHART"}, b)

    def test_markers_carry_the_keys(self):
        from frc.ledgers import p21_gravity as L
        data = json.loads((ROOT / "docs" / "21-gravity" / "21-gravity-ledger.json").read_text(encoding="utf-8"))
        keys = {r["label"]: r["key"] for b in data["blocks"] for r in b["rows"]}
        text = Path(L.__file__).read_text(encoding="utf-8")
        found = 0
        for line in text.splitlines():
            if re.match(r"\s*# 21:[A-Z]+\d+ \(p21\d{3}\)", line):
                for lab, key in re.findall(r"21:([A-Z]+\d+) \((p21\d{3})\)", line):
                    self.assertEqual(keys[lab], key); found += 1
                    if L.KEYS: self.assertEqual(L.KEYS[lab], key)
        self.assertEqual(found, len(L.PREDICATES))

    def test_rows_cited_exist(self):
        from frc.ledgers import p21_gravity as L
        data = json.loads((ROOT / "docs" / "21-gravity" / "21-gravity-ledger.json").read_text(encoding="utf-8"))
        labels = {r["label"] for b in data["blocks"] for r in b["rows"]}
        for pid, rows in L.LEDGER.items():
            for lab in rows.split(","):
                self.assertIn(lab.strip().split(":")[1], labels, pid)

    def test_chart_anchor(self):
        from frc import chart as C
        from frc import chart_gravity as CG
        self.assertEqual(CG.LN_OMEGA, 283.5)
        self.assertEqual(CG.LN_OMEGA, float(C.LN_OMEGA))


if __name__ == "__main__":
    unittest.main()
