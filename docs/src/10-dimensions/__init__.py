"""frc_10_dimensions — the validation package of *Dimensional Analysis over Finite Holographic Substrate*, installable:
    pip install frc-10-dimensions --find-links https://finitering.space/pkg/
    from frc_10_dimensions import predicate; predicate("10:C5")
The same files run in place from src/10-dimensions (python3 run_all.py)."""
from .dimcommon import predicate, verify_all, PREDICATES, LEDGER, LABELS, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "LABELS", "markers", "summary", "RESULTS"]
