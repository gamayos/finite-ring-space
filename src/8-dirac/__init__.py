"""frc_8_dirac — the validation package of *Schrödinger and Dirac Dynamics over Finite Substrate* (Akhtman, 2026), installable:
    pip install frc-8-dirac --find-links https://finitering.space/pkg/
    from frc_8_dirac import predicate; predicate("8:D9")
The same script runs in place from src/8-dirac (python3 dirac.py) and as a module (python3 -m frc_8_dirac)."""
from .dirac import predicate, verify_all, PREDICATES, LEDGER, LABELS, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "LABELS", "BLOCK", "markers", "summary", "RESULTS"]
