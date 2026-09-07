#!/usr/bin/env python3
"""Pin the two successor modules from observed Lean output only."""
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
FORMAL = HERE.parent
ROOT = FORMAL.parents[2]
LOGS = ROOT / "experiments/he_closure_costs/source_phase"
for module in ("Theory/BfvNoiseSource", "Assurance/ResidentBfvSourceWindow"):
    source = FORMAL / (module + ".lean")
    source_text = source.read_text()
    assert "#guard_msgs in\n#print axioms" not in source_text, "Preserve existing pins"
    logs = sorted(LOGS.glob("lean_" + source.stem + "_*.json"))
    latest = json.loads(logs[-1].read_text())
    assert latest["exit_code"] == 0
    messages = re.findall(
        r"('Minidregg\.[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms))",
        latest["stdout"],
    )
    by_name = {re.match("'([^']+)'", message).group(1): message for message in messages}
    names = re.findall(r"^#print axioms (\S+)$", source_text, re.M)
    assert len(names) == len(by_name)
    for name in names:
        message = by_name[name]
        assert "sorryAx" not in message
        source_text = source_text.replace(
            "#print axioms " + name + "\n",
            "/-- info: " + message + " -/\n#guard_msgs in\n#print axioms " + name + "\n",
        )
    source.write_text(source_text)
    print(module, len(names))
