"""Regenerate every figure produced for this paper, into ../figures/.

Runs each make_fig_*.py script. (Figure 1 and Figure 2 panels b,c are external assets
not regenerated here; make_fig_phase_a.py regenerates Figure 2 panel (a) with g=5.)
"""
import subprocess, sys, pathlib
here = pathlib.Path(__file__).resolve().parent
scripts = ["make_fig_sync.py", "make_fig_anatomy.py", "make_fig_shadow.py",
           "make_fig_rar.py", "make_fig_phase_a.py"]
ok = True
for s in scripts:
    print(f"=== {s} ===")
    p = subprocess.run([sys.executable, str(here/s)], capture_output=True, text=True)
    print(p.stdout, end="")
    if p.returncode != 0:
        ok = False
        print(p.stderr, file=sys.stderr)
print("\nALL FIGURES REGENERATED" if ok else "\nSOME FIGURES FAILED")
sys.exit(0 if ok else 1)
