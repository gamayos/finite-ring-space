"""frc_4_representation — the validation package of *Universal Latent Representation in Finite Ring Continuum* (Akhtman, Entropy 2026), installable:
    pip install frc-4-representation --find-links https://finitering.space/pkg/
    from frc_4_representation import predicate; predicate("4:C1")
The same script runs in place from src/4-representation (python3 representation.py) and as a module (python3 -m frc_4_representation)."""
from .representation import predicate, verify_all, PREDICATES, LEDGER, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "BLOCK", "markers", "summary", "RESULTS"]
