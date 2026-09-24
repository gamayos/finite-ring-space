"""frc_14_entropy — the validation package of *De Sitter Entropy Estimates over Finite Holographic Substrate*, installable:
    pip install frc-14-entropy --find-links https://finitering.space/pkg/
    from frc_14_entropy import predicate; predicate("14:C5")
The same script runs in place from src/14-entropy (python3 entropy.py) and as a module (python3 -m frc_14_entropy). The two
triangle blocks draw the paper's figures with matplotlib (REQUIRES, read by src/make_pkg.py into the sdist's dependencies)."""
REQUIRES = ["matplotlib"]
from .entropy import predicate, verify_all, PREDICATES, LEDGER, LABELS, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "LABELS", "BLOCK", "markers", "summary", "RESULTS", "REQUIRES"]
