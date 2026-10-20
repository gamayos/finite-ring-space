"""The ledger file of 25-godel (frc/ledgers/p25_godel.py; the 25-godel migration of 20 October 2026) and the logic theme's
primitives it uses (frc/logic.py: the trees, the prenex evaluator, the enumerated formulas over M_2 and their reader, the
certificate format; frc/diagonal.py: the name costs, k*(M), t(M) and the dense-coded instance): the counts against direct
enumerations, k*(M) and t(M) against the Lean's values (FRC.Diagonal.kstar, threshold) and the package's D5, the reader
against the enumerator's truth tables, the certificate verifier on a hand-built record, the decoders on a small field;
the ledger green, every check EXACT, its markers on its deciding checks, the consequence rows on their premises' markers,
its checks reproducing the package's records one for one."""
import itertools
import json
import random
import re
import unittest
from fractions import Fraction
from pathlib import Path

from frc import logic as LG
from frc import diagonal as DG

ROOT = Path(__file__).resolve().parents[2]

CONSEQUENCE_ROWS = {"25:C3": "A1", "25:G6": "D4", "25:H4": "F1", "25:J2": "B3"}     # named on their premises' markers (D4)
RETAGGED_I = {"25:F8", "25:G8", "25:G5"}                                            # python-corroborated, no Lean (20 October 2026)
# the Lean's values (lean/FrcCore/Theme/Threshold.lean, #eval) and the package's D5
KSTAR = {(2, 5): 2, (2, 9): 14, (2, 12): 33, (5, 6): 11}
THRESHOLD = {(2, 12): 396, (5, 6): 66}
FIFTEEN_PAIRS = {(2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (5, 5)}


def _rows(s): return [t.strip() for t in s.split(",") if t.strip()]


class LogicPrimitivesTest(unittest.TestCase):
    def test_trees_and_catalan(self):
        for l in range(1, 9):
            ts = LG.trees(l)
            self.assertEqual(len(ts), LG.catalan(l - 1))
            for p in (2, 3, 5, 13):
                self.assertTrue(all(LG.tree_value(t, p) == l % p for t in ts))
        self.assertEqual([LG.catalan(n) for n in range(8)], [1, 1, 2, 5, 14, 42, 132, 429])

    def test_formulas_M2_counts_and_reader(self):
        T4, _ = LG.formulas_M2(4, 9)
        self.assertEqual(sum(len(v) for v in T4.values()), 17820)
        T6, _ = LG.formulas_M2(6, 9)
        self.assertEqual(sum(len(v) for v in T6.values()), 65600)
        rnd = random.Random(25)
        pool = [f for v in T4.values() for f in v]
        for table, free, text in rnd.sample(pool, 400):            # the reader agrees with the enumerator's truth table
            for bits in range(16):
                env = {LG.VARS[i]: (bits >> i) & 1 for i in range(4)}
                r = LG.read_formula(text, 0, env)
                self.assertIsNotNone(r, text)
                self.assertEqual(r[1], len(text), text)
                self.assertEqual(bool(r[0]), bool((table >> bits) & 1), (text, bits))

    def test_prenex_evaluator(self):
        for p in (5, 7, 13):
            for text, pat, mat, want in LG.sentences(p):
                cnt = [0]
                self.assertEqual(LG.decide(p, pat, mat, cnt), want, text)
                self.assertEqual(cnt[0], p ** len(pat))                # the whole evaluation object, m^q leaves
        self.assertEqual(LG.next_prime_1mod4(10 ** 6), 1000033)
        self.assertEqual(LG.next_prime_1mod4(10 ** 18), 10 ** 18 + 9)

    def test_certificate_format(self):
        S = LG.Mp(13)
        rec = [("c", 1), ("c", 1), ("o", "+", 0, 1, 2), ("o", "*", 2, 2, 4), ("=", 3, 3)]
        accepted, values, cited, elems, lookups = LG.verify(rec, S)
        self.assertTrue(accepted)
        self.assertEqual(values[3], 4)
        self.assertEqual(lookups, 4)                                   # one lookup per constant and per operation step
        self.assertEqual(set(cited), {("+", 1, 1), ("*", 2, 2)})
        bad = [("c", 1), ("c", 1), ("o", "+", 0, 1, 3), ("=", 2, 2)]      # a wrong sum
        self.assertFalse(LG.verify(bad, S)[0])
        self.assertEqual(LG.eval_term(S, LG.term_of(rec, 3)), 4)
        W = LG.small_world(cited, elems, "+*", lambda op, x, y, U: U[0])    # the wrap: M' on the cited elements accepts the record
        self.assertTrue(LG.verify(rec, W)[0])
        self.assertTrue(set(W["U"]) <= set(range(13)) and len(W["U"]) <= lookups * 3)


class DiagonalTest(unittest.TestCase):
    def test_name_cost_by_enumeration(self):
        for a in (2, 3):
            names = sorted((len(w), w) for n in range(1, 6) for w in itertools.product(range(a), repeat=n))
            for k in (1, 2, 5, 10, 20):
                self.assertEqual(DG.name_cost(k, a), sum(l for l, _ in names[:k]))

    def test_kstar_and_threshold_against_lean(self):
        for (a, d), k in KSTAR.items(): self.assertEqual(DG.k_star(a, d), k, (a, d))
        for (a, d), t in THRESHOLD.items(): self.assertEqual(DG.threshold(a, d), t, (a, d))
        for a in range(2, 6):
            for d in range(1, 5): self.assertEqual(DG.k_star(a, d), 0, (a, d))      # no instance below five digits
        for a, d in FIFTEEN_PAIRS:                                                      # t(M) < a^(d-1) by the scan
            self.assertLess(DG.threshold(a, d), a ** (d - 1), (a, d))
            self.assertLess(DG.k_star(a, d), 6 * a ** (d // 3 + 1), (a, d))
        self.assertEqual(DG.last_k(5, 2, strict=True), 1)
        self.assertEqual(DG.last_k(9, 2, strict=True), 7)

    def test_admits_digit_form(self):
        # admits(k, k1, d, a) is the digit-form pair of inequalities; k* is the largest admitted k below the bound
        for a, d in ((2, 7), (3, 6)):
            bound = 6 * a ** (d // 3 + 1)
            passing = [k for k in range(1, bound) if any(DG.admits(k, k1, d, a) for k1 in range(1, d * k))]
            self.assertEqual(max(passing, default=0), DG.k_star(a, d))

    def test_decoders_on_a_small_field(self):
        dd = DG.dense(); g = dd.Gen(); V, Ev, show = dd.V, dd.Ev, dd.show
        for p in (17, 31):
            e = Ev(p)
            for J in range(5):
                if (1 << J) > p: break
                f = g.Int(V("x20"), J)
                self.assertEqual({x for x in range(p) if e.ev(f, {"x20": x})}, set(range(1 << J)))
                self.assertEqual(len(show(f)), 50 * J + 29)
        self.assertEqual(len(dd.primes_upto(131)), 32)


class GodelLedgerTest(unittest.TestCase):
    def test_ledger_green_and_kinds(self):
        from frc.ledgers import p25_godel as L
        for b in sorted(L.BLOCK): L.R.run_block(b)
        self.assertTrue(L.R.summary(write=False, expect=list(L.LEDGER)))
        self.assertEqual(len(L.LEDGER), 24)
        recs = {r["id"]: r for r in L.R.results}
        self.assertEqual(set(L.LEDGER), set(recs))
        for cid, r in recs.items():
            self.assertEqual(r["kind"], "EXACT", cid)
            self.assertTrue(r["ok"], cid)
            self.assertNotIn("[chart]", r["label"])
        self.assertEqual(set(L.LEDGER), set(L.FAMILY))
        self.assertTrue(all(v == f"godel.{k}" for k, v in L.FAMILY.items()))
        self.assertEqual(L.LEAN_ONLY, ())

    def test_markers_and_predicates(self):
        from frc.ledgers import p25_godel as L
        src = (ROOT / "frc" / "ledgers" / "p25_godel.py").read_text(encoding="utf-8")
        marks = L.R.markers()
        for pred, cid in L.PREDICATES.items():
            self.assertIn(pred, marks, pred)
            self.assertIn(pred, _rows(L.LEDGER[cid]), pred)
            key = L.KEYS[pred.split(":")[1]]
            self.assertRegex(src, rf"# (?:[^\n]*, )?{re.escape(pred)} \({key}\)")
        for pred, cid in CONSEQUENCE_ROWS.items(): self.assertEqual(L.PREDICATES[pred], cid, pred)
        witnessed = {r for v in L.LEDGER.values() for r in _rows(v)}
        self.assertEqual(witnessed, set(L.PREDICATES))
        self.assertEqual(len(witnessed), 28)
        path = ROOT / "docs" / "25-godel" / "25-godel-ledger.json"
        if path.exists():
            rows = json.loads(path.read_text(encoding="utf-8"))
            labels = {r["label"]: r for b in rows["blocks"] for r in b["rows"]}
            for pred in witnessed:
                lab = pred.split(":")[1]
                self.assertEqual(labels[lab]["tag"], "I" if pred in RETAGGED_I else "T", pred)
            for pred in witnessed - RETAGGED_I:                   # every T row the file witnesses has a core declaration
                self.assertIn("core", L.LEAN.get(pred.split(":")[1], ""), pred)

    def test_package_records_reproduced(self):
        from frc.ledgers import p25_godel as L
        rec = ROOT / "src" / "25-godel" / "results.json"
        if not rec.exists(): return
        d = json.loads(rec.read_text(encoding="utf-8"))
        self.assertEqual({r["id"] for r in d}, set(L.LEDGER))
        rows = {r["id"]: set(_rows(r["rows"])) for r in d}
        for cid, v in L.LEDGER.items():                           # the file cites what the package cited, plus the consequence rows
            self.assertTrue(rows[cid] <= set(_rows(v)), cid)
            self.assertTrue(set(_rows(v)) - rows[cid] <= set(CONSEQUENCE_ROWS), cid)


if __name__ == "__main__":
    unittest.main()
