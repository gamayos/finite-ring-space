"""
run_all.py — the 21-gravity validation package, end to end
===========================================================
Runs the twenty-one scripts of the suite through the registry (gravcommon), writes results.json — one record per
family, carrying the paper's ledger row(s) it witnesses — and exits nonzero if any family fails. Python 3.10+ with
numpy and sympy (mpmath); ≈ 1 minute (validate_branch's nonlinear solves and validate_fluxnoise's simulation dominate).

    python3 run_all.py

Families (one per script; the twelve of the paper's original suite first, then the eight of the round-01/02
revisions, then the uniqueness proof):
    newton ppn strongfield fp_gauge branch fluxnoise rar deepregime radiative orderone rotating primordial
    2pn 1pn_eih binding counting defect inertia deepregime_orbit fold_echo
    fierz_pauli
"""
import sys, time
import gravcommon

FAMILIES = ["grav." + s for s in [
    "newton", "ppn", "strongfield", "fp_gauge", "branch", "fluxnoise", "rar", "deepregime", "radiative", "orderone", "rotating", "primordial",
    "2pn", "1pn_eih", "binding", "counting", "defect", "inertia", "deepregime_orbit", "fold_echo",
    "fierz_pauli"]]

def main():
    t0 = time.time()
    for fam in FAMILIES:
        print(f"\n— {gravcommon.script_of(fam)}.py")
        gravcommon.run_block(fam)
    ok = gravcommon.summary(write=True)
    print(f"{len(gravcommon.RESULTS)} families, {len(gravcommon.MICRO)} micro-checks, {time.time() - t0:.0f} s; results.json written")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
