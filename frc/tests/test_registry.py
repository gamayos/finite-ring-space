"""frc.registry (task LM15): records, census, markers, one-predicate verification, and the results.json schema the site reads."""
import io, json, os, tempfile, unittest
from contextlib import redirect_stdout
from frc.registry import Registry

SOURCE = '''def block_A():
    # 99:A1 (p99001)
    R.check("A1", "one", True)

    # 99:A2 (p99002), 99:B1 (p99004)
    R.check("A2", "two", True)
'''


def quiet(f, *a, **k):
    with redirect_stdout(io.StringIO()): return f(*a, **k)


class RegistryTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.src = os.path.join(self.tmp.name, "toy.py")
        open(self.src, "w").write(SOURCE)
        self.R = Registry("99", "toy", {"A1": "99:A1", "A2": "99:A2, 99:B1", "B1": "99:B1"}, sources=[self.src])
        R = self.R

        @R.block("A", "the first block")
        def block_A():
            R.check("A1", "one", True); R.check("A2", "two", True)

        @R.block("B", "the second block")
        def block_B():
            R.check("B1", "three", self.b_ok, "detail", kind="[chart]")
        self.b_ok = True

    def tearDown(self): self.tmp.cleanup()

    def test_verify_all_and_census(self):
        self.assertTrue(quiet(self.R.verify_all))
        self.assertEqual([r["id"] for r in self.R.results], ["A1", "A2", "B1"])
        self.assertEqual(self.R.results[2]["kind"], "CHART")

    def test_failure_and_missing_check(self):
        self.b_ok = False
        self.assertFalse(quiet(self.R.verify_all))
        R2 = Registry("99", "toy", {"A1": "99:A1", "B1": "99:B1"})
        quiet(R2.check, "A1", "one", True)
        self.assertFalse(quiet(R2.summary, write=False, expect=["A1", "B1"]))
        self.assertRaises(KeyError, R2.check, "C9", "no such check", True)
        self.assertRaises(ValueError, R2.check, "A1", "bad kind", True, "", "GUESS")

    def test_markers(self):
        m = self.R.markers()
        self.assertEqual(m["99:A1"], ("toy.py", 2)); self.assertEqual(m["99:A2"], ("toy.py", 5)); self.assertEqual(m["99:B1"], ("toy.py", 5))

    def test_predicate_runs_the_citing_blocks(self):
        self.assertTrue(quiet(self.R.predicate, "99:B1"))
        self.assertEqual(sorted(self.R._ran), ["A", "B"])                  # B1 is decided in B and corroborated by A2
        self.assertIsNone(quiet(self.R.predicate, "99:Z9"))
        self.assertEqual(self.R.predicates, {"99:A1": "A1", "99:A2": "A2", "99:B1": "B1"})

    def test_results_json_schema(self):
        quiet(self.R.verify_all)
        path = os.path.join(self.tmp.name, "results.json")
        quiet(self.R.summary, write=True, path=path)
        recs = json.load(open(path))
        self.assertEqual(set(recs[0]), {"id", "rows", "block", "script", "label", "ok", "detail", "kind"})


if __name__ == "__main__":
    unittest.main()
