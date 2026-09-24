"""frc_3_causality — the validation package of *Euclidean–Lorentzian Dichotomy and Algebraic Causality in Finite Ring Continuum* (Akhtman, Entropy 2025), installable:
    pip install frc-3-causality --find-links https://finitering.space/pkg/
    from frc_3_causality import predicate; predicate("3:B2")
The same script runs in place from src/3-causality (python3 causality.py) and as a module (python3 -m frc_3_causality)."""
from .causality import predicate, verify_all, PREDICATES, LEDGER, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "BLOCK", "markers", "summary", "RESULTS"]
