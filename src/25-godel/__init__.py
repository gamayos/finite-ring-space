"""frc_25_godel — the validation package of *Incompleteness Without Infinity* (Akhtman, preprint 2026), installable:
    pip install frc-25-godel --find-links https://finitering.space/pkg/
    from frc_25_godel import predicate; predicate("25:F1")
The same script runs in place from src/25-godel (python3 godel.py) and as a module (python3 -m frc_25_godel)."""
from .godel import predicate, verify_all, PREDICATES, LEDGER, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "BLOCK", "markers", "summary", "RESULTS"]
