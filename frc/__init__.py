"""frc — the programme-wide framework of the Finite Ring Continuum (ledger migration, Phase 3, from 5 October 2026).

Three layers: the themes (`frc/<theme>.py`, mirrored in Lean by `lean/FrcCore` and `lean/FrcLedger`), the ledger files
(`frc/ledgers/`), and the presentation (one notebook per ledger). The theme map is `frc/themes.py`; `ci/gates.py`
enforces it. The base, structure and programme tiers are exact: integers and fractions only, standard library only.
Importing the package imports no theme.
"""
__version__ = "20261005"
