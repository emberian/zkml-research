#!/usr/bin/env bash
# Kernel-check the lane against warm dependencies; only emit into the local overlay.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
mini=/Users/ember/dev/minidregg
tc=/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin
build=$here/build
src=$mini/Assurance/CertificateAndDatalogCalculus.lean
mode=${1:-}
[[ $# == 0 || ( $# == 1 && $mode == --lean-only ) ]] || { echo "usage: $0 [--lean-only]" >&2; exit 2; }
mkdir -p "$build/Assurance"
cd "$build"
"$tc/lean" --version | tee lean-version.log
grep -q 'version 4\.35\.0,' lean-version.log
export PYTHONDONTWRITEBYTECODE=1
bash "$mini/scripts/check-import-boundary.sh"
python3 -IB - "$mini" "$src" <<'PY'
from pathlib import Path
import re, sys
sys.path.insert(0, str(Path(sys.argv[1]) / "scripts"))
from lean_imports import header_imports, _skip_blank
source = Path(sys.argv[2]).read_text()
imports = header_imports(source)
allowed = {"Mathlib", "Theory", "Pred", "Kernel", "Compiler", "Selvage", "Assurance"}
assert imports and all(i.split(".")[0] in allowed for i in imports), imports
lines = len(source.splitlines())
assert lines < 950, lines
# Skip nested Lean comments and strings before matching tokens or message guards.
parts = []
i = 0
while i < len(source):
    j = _skip_blank(source, i)
    if j != i:
        parts.append(" ")
        i = j
    elif source[i] == '"':
        m = re.match(r'"(?:\\.|[^"\\])*"', source[i:], re.S)
        assert m, "unterminated string"
        parts.append('""')
        i += m.end()
    else:
        parts.append(source[i])
        i += 1
code = "".join(parts)
bad = re.search(r"\b(sorry|sorryAx|admit|axiom|native_decide)\b|#guard\b", code)
assert not bad, bad.group()
pins = re.findall(r"#guard_msgs\s+in\s+#print\s+axioms\s+(\w+)", code)
assert {"cert_conj_shared_commit", "cert_sampled_audit", "cert_bpe_byte_weld",
        "cert_opened_byte_turn", "datalog_cert_sound_and_complete"}.issubset(pins)
assert len(pins) == len(re.findall(r"#print\s+axioms\b", code)), "unguarded axiom print"
print(f"ATLAS: {lines} lines, {len(pins)} axiom pins, imports and forbidden tokens checked")
PY

# Only the dependency search path is read from Lake. Always elaborate the lane source afresh.
deps=$("$tc/lake" --dir "$mini" env printenv LEAN_PATH)
export LEAN_PATH="$build:$deps"
"$tc/lean" -DwarningAsError=true -R "$mini" -o "$build/Assurance/CertificateAndDatalogCalculus.olean" "$src"
python3 -IB - "$tc/lean" "$mini/prover/testdata/cert_datalog_conformance.json" <<'PY'
import json, subprocess, sys
from pathlib import Path

lean, fixture = sys.argv[1:]
data = json.loads(Path(fixture).read_text())
assert data["schema"] == "minidregg.w11.cert_datalog_conformance.v1"
t = data["toy"]
assert t["root"] == t["expectedRoot"] == 839753907
assert t["depth"] == 4 and len(t["rules"]) == 10
assert [p["index"] for p in t["paths"]] == list(range(16))
rows = t["certs"] + t["generatedCerts"]
assert len(t["certs"]) == 7 and sorted(r["query"] for r in t["generatedCerts"]) == list(range(51))

# Translate only bounded integers, booleans and the four ground constructors into Lean data.
# The verifier and the soundness theorem come directly from the freshly elaborated module.
def nat(n, limit=2**64):
    assert type(n) is int and 0 <= n < limit, n
    return str(n)

def boolean(v):
    assert type(v) is bool, v
    return str(v).lower()

def seq(xs, render=nat):
    return "[" + ", ".join(map(render, xs)) + "]"

def atom(n):
    return nat(n, 51)

def key(n):
    return nat(n, 64)

def gr(r):
    return f"⟨{atom(r['head'])}, {seq(r['pos'], atom)}, {seq(r['neg'], atom)}⟩"

def claim(c):
    j = c["just"]
    kind = j["kind"]
    if kind == "memb":
        term = f".memb {nat(j['j'])} {nat(j['salt'])} {seq(j['path'])}"
    elif kind == "rule":
        assert j["subst"] == []
        rid = int(nat(j["ruleId"], len(t["rules"])))
        term = ".rule " + gr(t["rules"][rid])
    elif kind == "gap":
        def side(prefix):
            return f"({key(j[prefix+'Key'])}, {nat(j[prefix+'Salt'])}) {seq(j[prefix+'Path'])}"
        term = f".gap {nat(j['i'])} {side('left')} {side('right')}"
    elif kind == "unf":
        term = ".unf " + seq(j["u"], atom)
    else:
        raise ValueError(kind)
    return f"⟨{atom(c['atom'])}, {boolean(c['pos'])}, {nat(c['rank'])}, {term}⟩"

code = ["import Assurance.CertificateAndDatalogCalculus",
        "open Minidregg.Assurance.CertificateAndDatalogCalculus",
        "example : ∃ cw : CollisionWitness (fun _ : Bool => ()), cw.w₁ = true ∧ cw.w₂ = false :=",
        "  shared_commit_opening_binding (cm := ()) ⟨by decide, rfl, rfl⟩",
        "example : Judg (id : Bool → Bool) (exactVerify id (· = true)) (fun _ w => w)",
        "    (fun w => Bool.not w = false) 0 (fun _ _ => False) :=",
        "  cert_transducer_pushforward (R₁ := fun x : Bool => x = true) (R₂ := fun y : Bool => y = false)",
        "    (commit := (id : Bool → Bool)) (V := exactVerify id (· = true)) (E := fun _ w => w)",
        "    Bool.not (exact_opening_judg id (· = true)) (fun _ h => by cases h; rfl)",
        "abbrev ToyClaim := Claim (Fin 51) (Fin 64) Nat Nat",
        "instance (c : ToyClaim) : Decidable (Faithful toyEnc toyLeaves c) := by",
        "  unfold Faithful; split <;> infer_instance",
        f"example : toyRules = {seq(t['rules'], gr)} := by decide"]
for i in range(16):
    code.append(f"example : toyLeaves {i} = ({key(t['leafKeys'][i])}, {nat(t['leafSalts'][i])}) := by decide")
    code.append(f"example : mkPath toyH 4 toyLeaves {i} = {seq(t['paths'][i]['siblings'])} := by decide")
    code.append(f"example : toyH (.leaf (toyLeaves {i}).1 (toyLeaves {i}).2) = {nat(t['leafHashes'][i])} := by decide")
strata = [b["stratum"] for b in t["strata"] for _ in range(b["lo"], b["hi"]+1)]
code.append(f"example : (List.finRange 51).map toySt = {seq(strata)} := by decide")
names = {"cert_alert_bob": "certAlertBob", "cert_alert_alice_false": "certAlertAliceFalse",
         "cert_p_false": "certPFalse", "cert_cyclic": "certCyclic", "cert_nonadjacent_gap": "certNonAdjacent"}
results = []
for i, row in enumerate(rows):
    q, sg = atom(row["query"]), boolean(row["sign"])
    code.append(f"def cs{i} : List ToyClaim := {seq(row['claims'], claim)}")
    if row.get("name") in names:
        code.append(f"example : cs{i} = {names[row['name']]} := by decide")
    results.append(f"verifyDatalogCert toyProg toyH toyEnc 4 toyRoot {q} {sg} cs{i}")
    assert row["expect"] in ("accept", "reject")
    if i >= len(t["certs"]):
        assert row["expect"] == "accept"
        assert row["sign"] == (row["query"] in t["edb"] + t["modelTrue"])
        code.extend([f"example : SM toyProg (edbOf toyEnc 4 toyLeaves) {q} ↔ {sg} = true := by",
                     f"  apply (toy_signed_iff {q} {sg}).mp",
                     f"  exact ⟨cs{i}, by decide, by decide⟩"])
code.extend(["def main : IO Unit := do", "  IO.println (mroot toyH 4 toyLeaves)",
             "  IO.println (reprStr ([" + ", ".join(results) + "] : List Bool))"])
probe = Path("Parity.lean")
probe.write_text("\n".join(code) + "\n")
out = subprocess.run([lean, "-DwarningAsError=true", "--run", str(probe)], text=True, stdout=subprocess.PIPE)
if out.returncode:
    sys.exit(out.stdout or out.returncode)
root, verdicts = out.stdout.strip().split("\n", 1)
assert json.loads(root) == t["root"]
got = json.loads(verdicts)
assert got == [row["expect"] == "accept" for row in rows], got
print(f"Lean/JSON: root {root}; 16 paths; {len(rows)} matching verdicts; 51 signed model answers proved")
PY

[[ $mode != --lean-only ]] || exit 0
cd "$mini/prover"
export CARGO_TARGET_DIR=/tmp/target-w11-calculus
unset CERT_DATALOG_REGEN
cargo test --locked --release --lib datalog_and_cert_calculus 2>&1 | tee "$build/rust-lib.log"
cargo test --locked --release --test cert_and_datalog_calculus -- --nocapture --test-threads=1 2>&1 | tee "$build/rust-integration.log"
if grep -E '^warning(:|\[)' "$build"/rust-{lib,integration}.log; then
    echo 'Rust emitted a warning' >&2
    exit 1
fi
for log in "$build"/rust-{lib,integration}.log; do
    grep -Eq '^test result: ok\. [1-9][0-9]* passed; 0 failed; 0 ignored;' "$log"
done
echo 'PASS: Lean overlay, conformance parity and both release test targets'
