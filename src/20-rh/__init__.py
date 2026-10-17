"""frc_20_rh — the validation package of *Riemann Hypothesis over Finite Holographic Substrate* (Akhtman & Voether, 2026), installable:
    pip install frc-20-rh --find-links https://finitering.space/pkg/
    from frc_20_rh import predicate; predicate("20:B12")
The same script runs in place from src/20-rh (python3 rh.py) and as a module (python3 -m frc_20_rh). The blocks compute in exact
integer arithmetic (the standard library) and read the chart with numpy, and redraw the paper's two figures with matplotlib
(REQUIRES, read by src/make_pkg.py into the sdist's dependencies)."""
REQUIRES = ["numpy", "matplotlib"]
from .rh import predicate, verify_all, PREDICATES, LEDGER, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "BLOCK", "markers", "summary", "RESULTS", "REQUIRES"]
