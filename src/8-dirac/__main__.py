"""python3 -m frc_8_dirac [fin|shell|o2|o7|o134|o8|lat|o9 ...]: the script end to end (results.json in the working directory), or the named blocks."""
import runpy
runpy.run_module("frc_8_dirac.dirac", run_name="__main__", alter_sys=True)
