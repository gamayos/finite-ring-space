"""python3 -m frc_3_causality [A|B|C|D]: the script end to end (results.json in the working directory), or one block."""
import runpy
runpy.run_module("frc_3_causality.causality", run_name="__main__", alter_sys=True)
