# Supplementary Checks

Seven scripts, all exact arithmetic (no floats, no RNG); every number quoted
in the manuscript is reproduced by one of them. Run each with `python3`:

- `finite_checks.py` — the F_13 worked examples: power-map counts and loss
  factors, Cayley admissibility and orders (all trace-zero parameters),
  Clifford relations, boost conjugation, transported gammas, covariance
  sample. Frame F_13(t;0,1,2); the orientation i = g^{-kappa} = 5 is
  derived, not searched.
- `shell_checks.py` — the zonal-evolution theorem: drive-pullback
  eigenstructure (winding-k phase g^{-k} per chronon), isotropy pattern,
  sector separation; the F_17 example numbers (i = 4; A = 15, B = 1;
  |G_3| = 18; triality present at 17, absent at 13). 68 checks.
- `o2_checks.py` — the canonical Lorentzian coefficient: square classes of
  all named residues on every symmetry-complete shell p < 2000; nu = g
  canonical; the two admissibility anchors. 1048 checks.
- `o134_checks.py` — boost torus (kernel, Hilbert 90, cyclicity,
  triality), Cayley-transform bijection, period dichotomy (unipotent p /
  norm-one p+1), mixed-case datum ord(U) = 1563 at p = 5. 907 checks.
- `latitude_checks.py` — the latitude indices of the shell reading (time
  L_1, energy L_{kappa+1}; both dualities one capacity-shift; terminal
  latitude identities). 35 checks.
- `o7_checks.py` — the parity grading: squares = <g^2> (chronon parity),
  registered transport even, nu = c^2 (2g) factorization, parity split by
  admissibility class, synchronization gauge. 1735 checks.
- `o8_checks.py` — symmetric Dirac dynamics: gamma adjoint signs, the
  spinor twist X = g0 g1 g3 (Hermitian; all gammas X-anti-self-adjoint;
  the gamma0 recipe fails), D^s self-adjointness, X-unitary Cayley steps,
  massless p-power periods (25 at p = 5, 1+1) and massive factorization
  ord = lcm(p-power, ord phi(-m)) (75, 150); the cycle Laplacian on the
  phase cycle with the exact commuting free-interacting composite.
  32 checks.

Total: 3825 exact checks. Expected output of each script ends with
`N/N exact checks pass` (or the labelled True lines of `finite_checks.py`).
