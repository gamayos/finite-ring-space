"""The theme map and its gates (task LM14): the map is consistent, frc/README.md prints it, and ci/gates.py catches each
kind of breach in a scratch tree."""
import os, shutil, subprocess, sys, tempfile, unittest
from pathlib import Path
from frc import themes as TM

ROOT = Path(__file__).resolve().parents[2]


class MapTest(unittest.TestCase):
    def test_ranks_and_tiers(self):
        ranks = [t["rank"] for t in TM.THEMES.values()]
        self.assertEqual(len(ranks), len(set(ranks)))
        order = {t: i for i, t in enumerate(TM.TIERS)}
        by_rank = sorted(TM.THEMES.values(), key=lambda t: t["rank"])
        self.assertEqual([order[t["tier"]] for t in by_rank], sorted(order[t["tier"]] for t in by_rank))
        self.assertTrue(all(t["exact"] == (t["tier"] != "chart") for t in TM.THEMES.values()))
        self.assertLess(max(ranks), TM.KEYS["rank"]); self.assertLess(TM.KEYS["rank"], TM.LEDGERS["rank"])

    def test_every_file_once(self):
        fs = [f for k in ("py", "core", "ml") for f, *_ in TM.files(k)]
        self.assertEqual(len(fs), len(set(fs)))
        self.assertFalse(set(fs) & set(TM.LEGACY))

    def test_every_core_module_is_placed(self):
        core = {str(p.relative_to(ROOT)) for p in (ROOT / "lean" / "FrcCore").glob("*.lean")}
        placed = {f for f, *_ in TM.files("core")} | set(TM.LEGACY)
        self.assertEqual(sorted(core - placed), [])

    def test_readme_prints_the_map(self):
        self.assertIn(TM.markdown(), (ROOT / "frc" / "README.md").read_text(encoding="utf-8"))


GATE_CASES = {
    "python import upward": ("frc/shell.py", "from frc import carrier\n", "G09"),
    "float literal": ("frc/shell.py", "HALF = 0.5\n", "G09"),
    "math.sqrt": ("frc/shell.py", "import math\nR = math.sqrt(2)\n", "G09"),
    "third-party import": ("frc/shell.py", "import numpy\n", "G09"),
    "a ledger imported": ("frc/shell.py", "from frc.ledgers import p99_toy\n", "G09"),
    "core theme imports a paper module": ("lean/FrcCore/Theme/Extension.lean", "import FrcCore.Rh\n", "G09"),
    "the reals in an exact Mathlib theme": ("lean/FrcLedger/Theme/Extension.lean", "import Mathlib\ndef x : ℝ := 0\n", "G09"),
    "oversized core file": ("lean/FrcCore/Theme/Logic.lean", "-- x\n" * 801, "G10"),
    "a python file off the map": ("frc/misc.py", "X = 1\n", "G09"),
    "a Lean theme file off the map": ("lean/FrcCore/Theme/Misc.lean", "def x := 1\n", "G09"),
    "unbounded existential": ("lean/FrcCore/Theme/Numbers.lean", "theorem bad : ∀ n : Nat, ∃ m, n < m ∧ m % 2 = 0 := sorry\n", "G19"),
    "Infinite": ("lean/FrcCore/Theme/Numbers.lean", "theorem bad2 : Infinite Nat := sorry\n", "G19"),
}


class GateTest(unittest.TestCase):
    def run_gates(self, root):
        r = subprocess.run([sys.executable, "-B", str(ROOT / "ci" / "gates.py"), "all", f"--root={root}"], capture_output=True, text=True)
        return r.returncode, r.stdout

    def scratch(self):
        d = tempfile.mkdtemp()
        shutil.copytree(ROOT / "frc", Path(d) / "frc", ignore=shutil.ignore_patterns("tests", "__pycache__"))
        (Path(d) / "lean" / "FrcCore" / "Theme").mkdir(parents=True)
        (Path(d) / "lean" / "FrcLedger" / "Theme").mkdir(parents=True)
        (Path(d) / "frc" / "ledgers").mkdir(exist_ok=True)
        (Path(d) / "frc" / "ledgers" / "p99_toy.py").write_text("from frc import arith\n")
        (Path(d) / "lean" / "FrcCore" / "Rh.lean").write_text("-- a paper module\n")
        return d

    def test_clean_scratch_is_green(self):
        d = self.scratch()
        try:
            code, out = self.run_gates(d)
            self.assertEqual(code, 0, out)
        finally: shutil.rmtree(d)

    def test_each_breach_fails_its_gate(self):
        for name, (path, text, gate) in GATE_CASES.items():
            d = self.scratch()
            try:
                (Path(d) / path).write_text(text)
                code, out = self.run_gates(d)
                self.assertEqual(code, 1, f"{name}: {out}")
                self.assertIn(f"FAIL {gate}", out, name)
            finally: shutil.rmtree(d)

    def test_the_repository_is_green(self):
        code, out = self.run_gates(ROOT)
        self.assertEqual(code, 0, out)


if __name__ == "__main__":
    unittest.main()
