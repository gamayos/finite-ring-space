"""frc_1_algebra — the validation package of *Relativistic Algebra over Finite Ring Continuum* (Akhtman, Axioms 2025), installable:
    pip install frc-1-algebra --find-links https://www.finitering.space/pkg/
    from frc_1_algebra import row; row("1:B2")
The same files run in place from src/1-algebra (python3 run_all.py)."""
from .algcommon import row, verify_all, ROWS, LEDGER, SCRIPT, markers, summary, RESULTS
__all__ = ["row", "verify_all", "ROWS", "LEDGER", "SCRIPT", "markers", "summary", "RESULTS"]
