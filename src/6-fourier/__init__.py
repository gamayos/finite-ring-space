"""frc_6_fourier — the validation package of *Scale-Shift and Fractional Fourier Transform as Rotations over Finite Holographic
Substrate* (Akhtman, 2026; doi 10.20944/preprints202606.0127.v1), installable:
    pip install frc-6-fourier --find-links https://finitering.space/pkg/
    from frc_6_fourier import predicate; predicate("6:C3")
The same script runs in place from src/6-fourier (python3 fourier.py) and as a module (python3 -m frc_6_fourier). The blocks run on
numpy, block E draws the paper's entropy figure with matplotlib (REQUIRES, read by src/make_pkg.py into the sdist's dependencies)."""
REQUIRES = ["numpy>=1.24", "matplotlib>=3.7"]
from .fourier import predicate, verify_all, PREDICATES, LEDGER, BLOCK, markers, summary, RESULTS
__all__ = ["predicate", "verify_all", "PREDICATES", "LEDGER", "BLOCK", "markers", "summary", "RESULTS", "REQUIRES"]
