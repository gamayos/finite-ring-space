"""frc_5_reductio — the validation package of *Paradoxes of Infinity as Reductio ad Absurdum* (Akhtman, preprint 2025), installable:
    pip install frc-5-reductio --find-links https://finitering.space/pkg/
    from frc_5_reductio import predicate; predicate("5:E1")
The same script runs in place from src/5-reductio (python3 reductio.py) and as a module (python3 -m frc_5_reductio)."""
from .reductio import predicate, verify_all, PREDICATES, LEDGER, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "BLOCK", "markers", "summary", "RESULTS"]
