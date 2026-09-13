"""Run the full validation suite and report a PASS/FAIL summary."""
import subprocess, sys, pathlib

scripts = ["validate_newton.py", "validate_ppn.py", "validate_strongfield.py",
           "validate_fp_gauge.py", "validate_branch.py", "validate_fluxnoise.py", "validate_rar.py",
           "validate_deepregime.py", "validate_radiative.py", "validate_orderone.py", "validate_rotating.py", "validate_primordial.py"]
here = pathlib.Path(__file__).parent
results = {}
for s in scripts:
    print(f"\n=== {s} ===")
    p = subprocess.run([sys.executable, str(here/s)], capture_output=True, text=True)
    print(p.stdout, end="")
    if p.stderr.strip():
        print(p.stderr, end="", file=sys.stderr)
    results[s] = "PASS" in p.stdout.splitlines()[-1] if p.stdout else False
print("\n" + "="*46)
npass = sum(results.values())
for s, r in results.items():
    print(f"  {'PASS' if r else 'FAIL'}  {s}")
print(f"SUMMARY: {npass}/{len(scripts)} suites passed.")
sys.exit(0 if npass == len(scripts) else 1)
