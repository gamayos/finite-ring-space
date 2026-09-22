"""frc_10_dimensions — the validation package of *Dimensional Analysis over Finite Holographic Substrate*, installable:
    pip install https://www.finitering.space/pkg/frc-10-dimensions.tar.gz
    from frc_10_dimensions import row; row("10:C5")
The same files run in place from src/10-dimensions (python3 run_all.py)."""
from .dimcommon import row, verify_all, ROWS, LEDGER, LABELS, markers, summary, RESULTS
__all__ = ["row", "verify_all", "ROWS", "LEDGER", "LABELS", "markers", "summary", "RESULTS"]
