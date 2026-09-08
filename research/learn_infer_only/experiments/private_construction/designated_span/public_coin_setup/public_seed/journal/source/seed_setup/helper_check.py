"""Positive public SHAKE/encoding fixture only; no crypto backend or keygen."""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import derive

HERE = Path(__file__).resolve().parent
example = b"Nobody inspects the spammish repetition"
assert hashlib.shake_256(example).hexdigest(20) == "44709d6fcb83d92a76dcb0b668c98e1b1d3dafe7"
parts = [b"domain", b"seed", b"tau", bytes(4), (1).to_bytes(4, "big")]
encoded = derive.frame(parts)
offset = len(derive.QUERY_PREFIX)
count = int.from_bytes(encoded[offset:offset+4], "big")
offset += 4
decoded = []
for _ in range(count):
    size = int.from_bytes(encoded[offset:offset+8], "big")
    offset += 8
    decoded.append(encoded[offset:offset+size])
    offset += size
assert decoded == parts and offset == len(encoded)
domain = {"schema": "designated-complete-seed-domain-v1", "suite": derive.SUITE,
          "p_hex": "07", "q_hex": "03", "generator": 2, "dimension": 2,
          "row_count": 1, "rows": [[1, 1]], "pivot_columns": [0],
          "rejection_cap": derive.CAP,
          "complete_registry": [{"row_id": 0, "A": "02", "identity": "public-toy-only"}]}
first = derive.derive(domain)
assert first == derive.derive(domain)
for tape in first["tapes"]:
    upper = 3 if tape["role"] == "tau" else 7
    lower = 0 if tape["role"] == "tau" else 1
    for counter, word in enumerate(tape["raw_words_hex"], 1):
        raw = bytes.fromhex(word)
        expected = hashlib.shake_256(derive.query_bytes(derive.canonical(domain), derive.SEED,
                                  tape["role"], tape["coordinate"], counter)).digest(len(raw))
        assert raw == expected
        value = derive.candidate(raw, tape["word_bits"])
        assert (lower <= value < upper) == (counter == tape["accepted_counter"])
spec = importlib.util.spec_from_file_location("public_group", HERE/"source/public_setup/source/crypto/group.py")
group = importlib.util.module_from_spec(spec)
spec.loader.exec_module(group)  # constants only; no backend/native code
assert group.Q.bit_length() == 2047 and group.P.bit_length() == 2048
assert (1 << 2046) < group.Q and (1 << 2047) < group.P-1
parsed = []
for path in HERE.rglob("*.py"):
    ast.parse(path.read_text())
    parsed.append(str(path.relative_to(HERE)))
print(json.dumps({"ok": True, "scope": "positive public SHAKE/framing/truncation fixture and AST parsing only",
                  "shake256_documented_example_20_bytes": hashlib.shake_256(example).hexdigest(20),
                  "positive_toy_transcript": first,
                  "fixed_group_bits": {"tau": 2047, "U": 2048},
                  "availability_upper_bound": "577/2^128 in ideal independent-bit model",
                  "parsed_sources": sorted(parsed)}, indent=2))
