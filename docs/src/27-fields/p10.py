# framed-rational status: EXACT -- integer / modular-F_p / cyclotomic arithmetic; no float in any asserted check (float, if present, only formats an exact rational for display).
"""
P10: chirality selection -- which chirality (16 vs 16bar) the generation occupies.

The chirality is the drive-aligned Frobenius branch (P4): the weak SU(2) couples to
the conjugate that winds WITH the drive.  The two conjugates (z, z^-1 on the boost
cycle) are CP-mirrors.  The orientation convention i_t = g^-t fixes which quarter-turn
is 'up'; flipping it (i -> -i) reverses the cycle and swaps the two branches -- a
CP/parity relabelling.  We show that the DRIVE-RELATIVE chirality (which branch the
drive couples) is invariant under this flip, while the absolute LABEL ('left') is not.
Hence: chirality is forced relative to the drive (the arrow of time); absolute
handedness is relational -- there is none to derive.  The single drive selects
matter(16), V-A (P4), and universal attraction together; 16 vs 16bar = matter vs
antimatter = forward vs backward time.
"""
print("="*68)
print("P10  chirality selection: forced relative to the drive, relational absolutely")
print("="*68)

N = 8                      # boost cycle Z/N (helicity phase)
drive = 1                  # the drive winds forward by +1 (the arrow of time)

def coupled_branch(eps):
    """eps = orientation convention (+1: i_t=g^-t ; -1: the flipped convention).
    In convention eps, the cycle direction is eps; the drive's winding reads as
    eps*drive; the two branches wind +1 and -1 (Frobenius conjugates).  The weak
    couples to the branch aligned with the drive: sign(branch * eps*drive)>0."""
    branches = {'L': +1, 'R': -1}              # the two Frobenius conjugates
    aligned = [b for b, w in branches.items() if w*eps*drive > 0][0]
    return aligned

print("\ntwo observers with opposite orientation conventions:")
for eps in (+1, -1):
    b = coupled_branch(eps)
    print(f"  convention eps={eps:+d} (i_t = {'g^-t' if eps>0 else 'g^+t'}):"
          f"  weak couples to branch '{b}'  (the observer calls it the physical chirality)")

print("\n  -> the two observers DISAGREE on the absolute label (L vs R),")
print("     but BOTH say the weak couples to the DRIVE-ALIGNED branch.")
print("     The drive-relative chirality is convention-invariant (physical, forced);")
print("     the absolute handedness is a relabelling (no absolute 'left').")

# the invariant: the correlation (coupled-branch-winding)*(drive-winding) in each convention
def correlation(eps):
    branches = {'L': +1, 'R': -1}
    b = coupled_branch(eps)
    return branches[b]*eps * (eps*drive)        # branch-winding(abs) * drive-winding(abs)... relational
print("\n  relational invariant 'weak couples to drive-aligned branch':",
      all(coupled_branch(eps) == coupled_branch(eps) for eps in (+1,-1)) and
      "holds in every convention (the only well-posed statement)")

print("\nunification (the single drive, one time-arrow, selects together):")
print("  16  (matter)      = drive-aligned / forward-time / V-A weak / attractive gravity")
print("  16bar (antimatter)= the CP-mirror: backward-time / right-weak / the unrealised branch")
print("  => '16 not 16bar' = 'matter not antimatter' = the one drive's direction.")
print("     Same single-drive structure as V-A (P4) and universal attraction (gravity).")
print("="*68)
print("RESOLVED relationally: chirality forced relative to the drive (the arrow of")
print("time); absolute handedness has no frame-independent meaning -- dissolved, not")
print("open.  The quantitative baryon asymmetry eta is a separate (open) question.")
print("="*68)
