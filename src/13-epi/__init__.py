"""frc_13_epi — the validation package of *Finite Field Realisation of the Classical Constants π and e* (Akhtman, 2026), installable:
    pip install frc-13-epi --find-links https://finitering.space/pkg/
    from frc_13_epi import predicate; predicate("13:F2")
The same script runs in place from src/13-epi (python3 epi.py) and as a module (python3 -m frc_13_epi)."""
from .epi import predicate, verify_all, PREDICATES, LEDGER, LABELS, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "LABELS", "BLOCK", "markers", "summary", "RESULTS"]
