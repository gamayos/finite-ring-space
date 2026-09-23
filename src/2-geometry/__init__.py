"""frc_2_geometry — the validation package of *Geometry and Constants in Finite Ring Continuum* (Akhtman, Symmetry 2026), installable:
    pip install frc-2-geometry --find-links https://finitering.space/pkg/
    from frc_2_geometry import row; row("2:D1")
The same files run in place from src/2-geometry (python3 run_all.py)."""
from .geocommon import row, verify_all, ROWS, LEDGER, SCRIPT, markers, summary, RESULTS
__all__ = ["row", "verify_all", "ROWS", "LEDGER", "SCRIPT", "markers", "summary", "RESULTS"]
