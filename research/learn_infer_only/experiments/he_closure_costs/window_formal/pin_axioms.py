#!/usr/bin/env python3
"""Pin observed successful axiom messages; never infer or weaken a pin."""
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FORMAL = ROOT / "formal/he_closure_costs"
for source in sorted(FORMAL.glob("*/*.lean")):
    records = sorted(HERE.glob(f"lean_{source.stem}_*.json"))
    good = [json.loads(p.read_text()) for p in records if json.loads(p.read_text())["exit_code"] == 0]
    assert good, source
    messages = re.findall(r"('Minidregg\.[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms))", good[-1]["stdout"])
    by_name = {re.match("'([^']+)'", m).group(1): m for m in messages}
    text = source.read_text()
    if "#guard_msgs in\n#print axioms" in text:
        raise RuntimeError(f"{source} is already pinned; preserve the observed guard messages")
    for name in re.findall(r"^#print axioms (\S+)$", text, re.M):
        message = by_name[name]
        assert "sorryAx" not in message, (name, message)
        replacement = f"/-- info: {message} -/\n#guard_msgs in\n#print axioms {name}"
        text = text.replace(f"#print axioms {name}\n", replacement + "\n")
    source.write_text(text)
