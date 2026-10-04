"""python3 -m frc_25_godel [A|B|C|D|E|F|G]: the script end to end (results.json in the working directory), or one block."""
import runpy
runpy.run_module("frc_25_godel.godel", run_name="__main__", alter_sys=True)
