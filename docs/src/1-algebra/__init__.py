"""frc_1_algebra — the validation package of *Relativistic Algebra over Finite Ring Continuum* (Akhtman, Axioms 2025), installable:
    pip install frc-1-algebra --find-links https://finitering.space/pkg/
    from frc_1_algebra import predicate; predicate("1:B2")
The same files run in place from src/1-algebra (python3 run_all.py)."""
from .algcommon import predicate, verify_all, PREDICATES, LEDGER, SCRIPT, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "SCRIPT", "markers", "summary", "RESULTS"]
