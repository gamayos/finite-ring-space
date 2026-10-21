"""The ledger file of 5-reductio (frc/ledgers/p05_reductio.py; the 5-reductio migration of 21 October 2026) and the logic
theme's primitives it uses (frc/logic.py: the frame W_N and the Δ₀ constructors; frc/sets.py: Ackermann codes, the Russell
class, the iterated singletons, counting measure, the small groups, the walks): the frame against direct arithmetic, the
Δ₀ constructors against frc/formation.py's evaluators and the core's worked instance, the Russell class and the chain
against the Lean statements (no code is a member of itself, the chain's rank is its index), counting measure additive
and invariant, the ledger green, every check EXACT, its markers on its deciding checks, the consequence row D5 on its
premises' markers, the package's records reproduced one for one."""
import itertools
import json
import random
import re
import unittest
from pathlib import Path

from frc import logic as LG
from frc import formation as FM
from frc import sets as ST

ROOT = Path(__file__).resolve().parents[2]

CONSEQUENCE_ROWS = {"5:D5": "B1"}                       # named on its premises' markers (A1, B1, B3)
RETAGGED_I = {"5:D4"}                                   # python-corroborated, no Lean (21 October 2026); B2 and D7 have no check
OMEGA_ROWS = {"5:B7"}                                   # the Ω-hard row with a corroborating check (D2)


def _rows(s): return [t.strip() for t in s.split(",") if t.strip()]


class FramePrimitivesTest(unittest.TestCase):
    def test_frame_relations(self):
        W = LG.Frame(7)
        for x in range(7):
            for y in range(7):
                self.assertEqual(W.S(x, y), y == x + 1)
                self.assertEqual(W.lt(x, y), x < y)
                for z in range(7):
                    self.assertEqual(W.A(x, y, z), z == x + y)
                    self.assertEqual(W.M(x, y, z), z == x * y)
        self.assertFalse(W.S(6, 7)); self.assertFalse(W.A(4, 4, 8))        # overflow fails the atom

    def test_constructors_and_worked_instance(self):
        for n in range(6): self.assertEqual(FM.d0_term((), LG.num(n)), n)
        v = ("var", 0)
        self.assertTrue(FM.d0_eval((5,), LG.prime_form(0)))
        self.assertFalse(FM.d0_eval((6,), LG.prime_form(0)))
        g = LG.goldbach_form(20)
        self.assertTrue(FM.d0_eval((), g))
        self.assertEqual(FM.d0_bound((), g), 400)                          # the core's goldbach_ten_bound at M = 10 is 100
        self.assertEqual(FM.d0_bound((), LG.goldbach_form(10)), 100)
        for N in (401, 500):
            self.assertTrue(FM.d0_eval_frame(N, (), g))                    # stable above the bound (5:B6)
        even = LG.bex(v, ("eq", ("add", v, v), ("var", 1)))                  # ∃ x ≤ y, x + x = y: y is even
        self.assertFalse(FM.d0_eval((3,), even))
        self.assertTrue(FM.d0_eval((4,), even))
        self.assertTrue(FM.d0_eval((3,), LG.disj(even, ("neg", even))))
        self.assertTrue(FM.d0_eval((4,), LG.impl(even, even)))
        rng = random.Random(5)
        for _ in range(50):
            f = LG.random_form(rng, 2, 0)
            t = FM.d0_bound((), f)
            self.assertEqual(FM.d0_eval_frame(t + 1, (), f), FM.d0_eval((), f))


class SetsTest(unittest.TestCase):
    def test_ackermann_codes(self):
        for u in range(1 << 10):
            ms = ST.members(u)
            self.assertEqual(sum(1 << m for m in ms), u)
            self.assertNotIn(u, ms)                                        # no code is a member of itself (not_mem_self)
            self.assertEqual(ST.russell(u), u)                             # the Russell class of u is u (mem_russell)
            self.assertNotIn(ST.russell(u), ms)                            # and not a member of u (russell_not_mem_hf)
        for n in range(6):
            self.assertEqual(ST.rank(ST.chain(n)), n)                      # rank_chain
        self.assertEqual(len({ST.chain(n) for n in range(6)}), 6)          # chain_injective
        V = ST.hf_levels(4)
        self.assertEqual([len(level) for level in V], [0, 1, 2, 4, 16])

    def test_counting_measure(self):
        n = 6
        for A in range(1 << n):
            for B in range(1 << n):
                if A & B == 0:
                    self.assertEqual(ST.measure(A | B, n), ST.measure(A, n) + ST.measure(B, n))     # measure_add
            self.assertEqual(ST.measure(A, n) + ST.measure(~A & ((1 << n) - 1), n), n)             # measure_compl
        for sigma in itertools.permutations(range(n)):
            for A in (0b101010, 0b000111, 0b111111, 0):
                self.assertEqual(ST.measure(ST.image(A, sigma, n), n), ST.measure(A, n))            # measure_perm
        for k in (1, 2, 3):                                                                           # no_doubling
            self.assertFalse(any(len(set(f)) == 2 * k for f in itertools.product(range(k), repeat=2 * k)))

    def test_groups_and_walks(self):
        for name, order in (("Z2", 2), ("Z3", 3), ("S3", 6)):
            G = ST.perm_group(name)
            self.assertEqual(len(G), order)
            self.assertTrue(all(ST.compose(p, q) in G for p in G for q in G))
        edges = {(0, 1), (1, 2), (2, 0)}
        self.assertEqual(ST.longest_walk(range(3), edges), 4)              # a cycle: walks of every length (|cols| + 1)
        self.assertEqual(ST.longest_walk(range(3), {(0, 1), (1, 2)}), 2)


class ReductioLedgerTest(unittest.TestCase):
    def test_ledger_green_and_kinds(self):
        from frc.ledgers import p05_reductio as L
        for b in sorted(L.BLOCK): L.R.run_block(b)
        self.assertTrue(L.R.summary(write=False, expect=list(L.LEDGER)))
        self.assertEqual(len(L.LEDGER), 17)
        recs = {r["id"]: r for r in L.R.results}
        self.assertEqual(set(L.LEDGER), set(recs))
        for cid, r in recs.items():
            self.assertEqual(r["kind"], "EXACT", cid)
            self.assertTrue(r["ok"], cid)
        self.assertEqual(set(L.LEDGER), set(L.FAMILY))
        self.assertEqual(L.LEAN_ONLY, ())

    def test_markers_and_predicates(self):
        from frc.ledgers import p05_reductio as L
        src = (ROOT / "frc" / "ledgers" / "p05_reductio.py").read_text(encoding="utf-8")
        marks = L.R.markers()
        for pred, cid in L.PREDICATES.items():
            self.assertIn(pred, marks, pred)
            self.assertIn(pred, _rows(L.LEDGER[cid]), pred)
            key = L.KEYS[pred.split(":")[1]]
            self.assertRegex(src, rf"# (?:[^\n]*, )?{re.escape(pred)} \({key}\)")
        for pred, cid in CONSEQUENCE_ROWS.items(): self.assertEqual(L.PREDICATES[pred], cid, pred)
        witnessed = {r for v in L.LEDGER.values() for r in _rows(v)}
        self.assertEqual(witnessed, set(L.PREDICATES))
        self.assertEqual(len(witnessed), 20)
        path = ROOT / "docs" / "5-reductio" / "5-reductio-ledger.json"
        if path.exists():
            rows = json.loads(path.read_text(encoding="utf-8"))
            labels = {r["label"]: r for b in rows["blocks"] for r in b["rows"]}
            for pred in witnessed:
                lab = pred.split(":")[1]
                want = "I" if pred in RETAGGED_I else "Ω" if pred in OMEGA_ROWS else "T"
                self.assertEqual(labels[lab]["tag"], want, pred)
            for pred in witnessed - RETAGGED_I - OMEGA_ROWS:               # every T row the file witnesses has a core declaration
                self.assertIn("core", L.LEAN.get(pred.split(":")[1], ""), pred)
            for lab in ("B2", "D4", "D7"): self.assertEqual(labels[lab]["tag"], "I", lab)

    def test_package_records_reproduced(self):
        from frc.ledgers import p05_reductio as L
        rec = ROOT / "src" / "5-reductio" / "results.json"
        if not rec.exists(): return
        d = json.loads(rec.read_text(encoding="utf-8"))
        self.assertEqual({r["id"] for r in d}, set(L.LEDGER))
        rows = {r["id"]: set(_rows(r["rows"])) for r in d}
        for cid, v in L.LEDGER.items():                                   # the file cites what the package cited, plus D5
            self.assertTrue(rows[cid] <= set(_rows(v)), cid)
            self.assertTrue(set(_rows(v)) - rows[cid] <= set(CONSEQUENCE_ROWS), cid)


if __name__ == "__main__":
    unittest.main()
