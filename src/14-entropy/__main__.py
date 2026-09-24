"""python3 -m frc_14_entropy [est|tri|cap]: the script end to end (results.json in the working directory, the figures in the package's out/), or one block."""
import runpy
runpy.run_module("frc_14_entropy.entropy", run_name="__main__", alter_sys=True)
