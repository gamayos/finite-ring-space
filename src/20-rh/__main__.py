"""python3 -m frc_20_rh [A|B|C|D|E ...]: the script end to end (results.json and figures/ in the working directory), or the blocks named."""
import runpy
runpy.run_module("frc_20_rh.rh", run_name="__main__", alter_sys=True)
