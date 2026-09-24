"""frc_10_dimensions — the validation package of *Dimensional Analysis over Finite Holographic Substrate*, installable:
    pip install frc-10-dimensions --find-links https://finitering.space/pkg/
    from frc_10_dimensions import predicate; predicate("10:C5")
The same script runs in place from src/10-dimensions (python3 dimensions.py) and as a module (python3 -m frc_10_dimensions)."""
from .dimensions import predicate, verify_all, PREDICATES, LEDGER, LABELS, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "LABELS", "BLOCK", "markers", "summary", "RESULTS"]
