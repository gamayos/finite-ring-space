"""frc_1_algebra — the validation package of *Relativistic Algebra over Finite Ring Continuum* (Akhtman, Axioms 2025), installable:
    pip install frc-1-algebra --find-links https://finitering.space/pkg/
    from frc_1_algebra import predicate; predicate("1:B2")
The same script runs in place from src/1-algebra (python3 algebra.py) and as a module (python3 -m frc_1_algebra)."""
from .algebra import predicate, verify_all, PREDICATES, LEDGER, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "BLOCK", "markers", "summary", "RESULTS"]
