#!/usr/bin/env python3
"""Re-extract only local mirrored papers, then rerun the finite premise audit."""
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
source = here / "source"
source.mkdir(exist_ok=True)
mirror = Path("/Users/ember/dev/gh/forks/IACR-eprint-mirror")
for year, identifier in ((2017, 276), (2017, 274), (2019, 1010)):
    subprocess.run(["pdftotext", "-layout", str(mirror / str(year) / f"{identifier}.pdf"),
                    str(source / f"{year}-{identifier}.txt")], check=True)
with (here / "stdout.txt").open("w") as out:
    subprocess.run([sys.executable, "-B", str(here / "audit.py")], stdout=out, check=True)
