"""python3 -m frc_13_epi [e|pi|pi2|tow|kur|frm ...]: the script end to end (results.json in the working directory), or the blocks named."""
import runpy
runpy.run_module("frc_13_epi.epi", run_name="__main__", alter_sys=True)
