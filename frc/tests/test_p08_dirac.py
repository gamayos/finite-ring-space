"""8-dirac's ledger file (frc/ledgers/p08_dirac.py): the ledger file green, its markers on its deciding checks with the keys
of the generated table, every witnessed predicate decided by a check that cites it, every block exact (no chart), and the
instances the paper names (the laboratory Subjects 𝔽₁₃ and 𝔽₁₇₃ with the drive 2, the shell 𝔽₅ for the dense spinor
computations, the laboratory Carrier)."""
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
    from frc.ledgers import p08_dirac as L
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
        self.assertEqual(L.PAPER, "8-dirac")
        for lab, pid in L.PREDICATES.items():
            self.assertIn(lab, [x.strip() for x in L.LEDGER[pid].split(",")])
        for lab in L.LEAN:
            self.assertTrue(f"8:{lab}" in L.PREDICATES or lab in L.LEAN_ONLY, lab)
        self.assertEqual(L.LEAN_ONLY, ())
        self.assertEqual(set(L.BLOCK), {"B", "C", "D", "E", "F", "X"})
        kinds = {b: {r["kind"] for r in L.R.results if r["id"][0] == b} for b in L.BLOCK}
        for b in L.BLOCK: self.assertEqual(kinds[b], {"EXACT"}, b)
        self.assertEqual(L.SHELLS, [(13, 2), (173, 2)])
        self.assertEqual(L.DENSE, (5, 2))
        self.assertEqual(L.CARRIER, (2408561, 602140, 6))
        self.assertEqual((L.P, L.G), (13, 2))

    def test_markers_carry_the_keys(self):
        from frc.ledgers import p08_dirac as L
        data = json.loads((ROOT / "docs" / "8-dirac" / "8-dirac-ledger.json").read_text(encoding="utf-8"))
        keys = {r["label"]: r["key"] for b in data["blocks"] for r in b["rows"]}
        text = Path(L.__file__).read_text(encoding="utf-8")
        found = 0
        for line in text.splitlines():
            if re.match(r"\s*# 8:[A-Z]+\d+ \(p\d{5}\)", line):
                for lab, key in re.findall(r"8:([A-Z]+\d+) \((p\d{5})\)", line):
                    self.assertEqual(keys[lab], key); found += 1
                    if L.KEYS: self.assertEqual(L.KEYS[lab], key)
        self.assertEqual(found, len(L.PREDICATES))

    def test_rows_cited_exist(self):
        from frc.ledgers import p08_dirac as L
        data = json.loads((ROOT / "docs" / "8-dirac" / "8-dirac-ledger.json").read_text(encoding="utf-8"))
        labels = {r["label"] for b in data["blocks"] for r in b["rows"]}
        for pid, rows in L.LEDGER.items():
            for lab in rows.split(","):
                self.assertIn(lab.strip().split(":")[1], labels, pid)
        witnessed = {r["label"] for b in data["blocks"] for r in b["rows"] if r.get("tag") == "T"}
        self.assertEqual(witnessed, {lab.split(":")[1] for lab in L.PREDICATES})         # every T row has a deciding check

    def test_lean_table(self):
        from frc.ledgers import p08_dirac as L
        self.assertTrue(all(v in ("core", "ml", "core, ml") for v in L.LEAN.values()))
        self.assertEqual(len(L.LEAN), 44)                                    # the rows with a Lean declaration (the record schema of 2 November 2026)
        self.assertEqual(len(L.PREDICATES), 48)                              # one check per theorem row


if __name__ == "__main__":
    unittest.main()
