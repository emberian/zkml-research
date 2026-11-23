"""Emit the pinned Obend input and expected-output records using its pure Lean definitions."""
import argparse
from pathlib import Path
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument("obend", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
pin = "25dd6789"
base = "lean/Obend/Lower/Pancake/"


def source(path):
    return subprocess.check_output(["git", "-C", args.obend, "show", f"{pin}:{path}"], text=True)


def excerpt(text, start, end):
    return text[text.index(start):text.index(end, text.index(start))]


model = source(base + "BeltLatch.lean")
test = source("lean/tests/metasystem/PancakeBeltLatchTest.lean")
standalone = "\n".join([
    "import Std",
    "namespace PancakeBeltLatchTest",
    excerpt(source(base + "PanSem.lean"), "abbrev Word :=", "\n"),
    excerpt(model, "structure Digest where", "private def digestAt"),
    excerpt(test, "private def initial", "private def fixture"),
    """
def emitRecords (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "expected an output path")
  let mut result := ByteArray.empty
  for (s, r, v) in vectors do
    let (actual, next) := stepBeltLatch s r
    unless actual = v do throw (IO.userError "invalid vector")
    result := result ++ bytes (stateWords s ++ requestWords r)
    result := result ++ bytes ([v.code] ++ stateWords next ++ requestWords r)
  IO.FS.writeBinFile out result
  IO.println s!"{vectors.length} Lean records, {result.size} bytes"
end PancakeBeltLatchTest
def main := PancakeBeltLatchTest.emitRecords
""",
])
scratch = Path(__file__).resolve().parents[2] / "native/target"
scratch.mkdir(parents=True, exist_ok=True)
with tempfile.TemporaryDirectory(dir=scratch) as tmp:
    lean = Path(tmp) / "Vectors.lean"
    lean.write_text(standalone)
    version = source("lean/lean-toolchain").strip()
    subprocess.run(["lean", "+" + version, "--run", lean, args.output.resolve()], check=True)
