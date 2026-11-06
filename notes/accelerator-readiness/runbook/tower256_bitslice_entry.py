"""Kaggle entry, accel-tower-bitslice-01: the workload-2 script, shrunk and offline, with the
bit-sliced multiply checked, timed, and used in the encode and folds."""
import os
import runpy
import sys

os.environ["TOWER256_GPU_ARGS"] = "--mul bs --bitslice-bench"
sys.argv = ["kaggle_entry.py"] + sys.argv[1:]
runpy.run_path("kaggle_entry.py", run_name="__main__")
