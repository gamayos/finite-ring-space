"""frc_2_geometry — the validation package of *Geometry and Constants in Finite Ring Continuum* (Akhtman, Symmetry 2026), installable:
    pip install frc-2-geometry --find-links https://finitering.space/pkg/
    from frc_2_geometry import predicate; predicate("2:D1")
The same script runs in place from src/2-geometry (python3 geometry.py) and as a module (python3 -m frc_2_geometry)."""
from .geometry import predicate, verify_all, PREDICATES, LEDGER, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "BLOCK", "markers", "summary", "RESULTS"]
