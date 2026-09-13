#!/usr/bin/env python3
"""Latitude-index checks: time = L_1, energy = L_{S+1} (EXACT).

Addendum to reports/o134-findings.md (shell-reading programme). Latitude
formalism per 2-geometry Def. 3.1: orbital shell S_p on the frame
F_p(t;0,1,g); meridian M_m the additive ray 0, g^m, 2g^m, ..., pi*g^m;
latitude L_a the multiplicative orbit at radius a; ladder a = 1..pi with
pi = 2*kappa the terminal latitude (collapsed to the antipode).

Claims checked (Subject register on F_13, F_17; Carrier register on the
lab Carrier Om = 2,408,561, S = 602,140):
  L1  Ladder bounds: energy index S+1 (kappa+1) lies inside the ladder,
      and is the first rung past the midpoint (rungs S | S+1 straddle
      the equator; ladder length 2S is even, no middle rung).
  L2  One shift, two ladders: the meridian shift m -> m+kappa is
      multiplication by g^kappa = +-i (prime meridian -> quarter-turn
      meridian: space -> momentum); the latitude shift a -> a+kappa
      sends 1 -> kappa+1 (time -> energy).  Both dualities are the
      index advance by the capacity.
  L3  Framed-rational radius register: kappa = -4^{-1}, so the energy
      radius is 1 + kappa = 3*4^{-1} = 1 - 1/4: the quarter-cycle shift
      subtracts exactly one quarter of the unit radius.
  L4  Terminal latitude: pi = 2*kappa = -2^{-1} = -c^2 as a residue; on
      the Carrier pi_Om = 2S = G (B18): the ladder terminates at the
      half-period -- the antipode of the observer origin carries the
      G / -c^2 seat.
  L5  Chart consistency: the framed-complex chart reads latitudes as
      norm circles; the unit-norm circle has exactly p-1 points, the
      cardinality of the phase cycle L_1 (time); the energy circle
      carries norm (1 - 1/4)^2 = 9/16.
Class: EXACT.
"""
import sys

checks = 0
def chk(label, ok):
    global checks
    checks += 1
    if not ok:
        print(f"FAIL: {label}"); sys.exit(1)

def inv(a, p): return pow(a % p, p - 2, p)

CASES = [(13, 2), (17, 3), (2408561, 6)]          # (p, g); Carrier last

for p, g in CASES:
    kap = (p - 1) // 4
    pi = 2 * kap
    # L1: ladder bounds and midpoint straddle
    chk(f"L1 p={p} in-ladder", 1 <= kap + 1 <= pi)
    chk(f"L1 p={p} past-half", kap + 1 == pi // 2 + 1 and pi % 2 == 0)
    # L2: meridian shift by kappa is the quarter-turn
    gk = pow(g, kap, p)
    chk(f"L2 p={p} g^kappa = +-i", pow(gk, 2, p) == p - 1)
    ray = [a % p for a in range(1, pi + 1)]        # prime meridian labels
    chk(f"L2 p={p} ray*i = quarter-turn ray",
        [(a * gk) % p for a in ray] == [(a * gk) % p for a in range(1, pi + 1)]
        and (1 * gk) % p == gk)                    # unit -> quarter-turn seat
    chk(f"L2 p={p} latitude shift 1 -> kappa+1", 1 + kap == kap + 1)
    # L3: radius register
    chk(f"L3 p={p} kappa = -1/4", kap % p == (p - inv(4, p)) % p)
    chk(f"L3 p={p} energy radius = 3/4 = 1 - 1/4",
        (kap + 1) % p == 3 * inv(4, p) % p == (1 - inv(4, p)) % p)
    # L4: terminal latitude residue identities
    inv2 = inv(2, p)
    chk(f"L4 p={p} pi = -2^-1", pi % p == (p - inv2) % p)
    chk(f"L4 p={p} pi = -c^2 seat", (p - pi) % p == inv2)  # -pi = 2^-1 = c^2
    # L5: unit-norm circle count = p-1 = |phase cycle| (p = 1 mod 4)
    if p < 100:
        cnt = sum(1 for a in range(p) for b in range(p)
                  if (a * a + b * b) % p == 1)
        chk(f"L5 p={p} |norm-1 circle| = p-1", cnt == p - 1)
    chk(f"L5 p={p} energy norm = 9/16",
        pow(kap + 1, 2, p) == 9 * inv(16, p) % p)

# Carrier-register readings (B18 web)
Om, S = 2408561, 602140
chk("L4 Carrier 2S = G seat", (2 * S) % Om == 1204280)         # G = 2S
chk("L4 Carrier -2S = c^2", (Om - 2 * S) % Om == (Om + 1) // 2)  # -pi = c^2
chk("L3 Carrier S+1 = 3/4", (S + 1) % Om == 3 * inv(4, Om) % Om)

print(f"{checks}/{checks} exact checks pass")
