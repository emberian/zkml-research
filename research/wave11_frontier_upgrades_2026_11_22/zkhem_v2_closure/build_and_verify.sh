#!/usr/bin/env bash
# Compile only the owned module. Installed package oleans are read-only inputs.
set -euo pipefail
cd "$(dirname "$0")"
lane=$(pwd -P)
md=/Users/ember/dev/minidregg
ds=/Users/ember/dev/dregg-sig
lean=/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
module=Selvage/ZkHemV2SoundnessAndPrivacy
export PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0
status_hash() { git -C "$ds" status --short | shasum -a 256 | cut -d' ' -f1; }
before=$(status_hash)
echo "dregg-sig before $before"
finish() {
    local rc=$? after
    after=$(status_hash) || exit 1
    echo "dregg-sig after  $after"
    [[ "$before" == "$after" ]] || exit 1
    exit "$rc"
}
trap finish EXIT

export CARGO_TARGET_DIR=/tmp/target-w11-zkhem
mkdir -p "$CARGO_TARGET_DIR"
cargo test --release --locked 2>&1 | tee "$CARGO_TARGET_DIR/w11-verification.log"
if grep -E '(^|: )warning:' "$CARGO_TARGET_DIR/w11-verification.log"; then exit 1; fi

bash "$md/scripts/check-import-boundary.sh"
python3 - "$md" "$module" <<'PY'
from pathlib import Path
import json, re, sys
root, module = sys.argv[1:]
sys.path.insert(0, str(Path(root) / 'scripts'))
from lean_imports import header_imports
src = (Path(root) / (module + '.lean')).read_text()
imports = header_imports(src)
assert imports and all(i.split('.')[0] in {'Mathlib','Theory','Selvage'} for i in imports), imports
code = re.sub(r'/\-.*?\-/|--[^\n]*', '', src, flags=re.S)
assert not re.search(r'\b(sorry|sorryAx|admit|axiom|native_decide)\b', code)
pins = re.findall(r'#guard_msgs \(whitespace := lax\) in #print axioms (\w+)', code)
assert len(pins) >= 38 and len(pins) == code.count('#print axioms')
lines = len(src.splitlines())
assert lines < 950, lines
print(f'{lines} Lean lines, {len(pins)} pinned axiom reports, allowed imports, no forbidden tokens')

d = json.loads(Path('zkhem_v2_conformance.json').read_text())
ledger = src.split('def v2LedgerRows', 1)[1].split('def rowCertified', 1)[0]
rows = [tuple(map(int, x)) for x in re.findall(r'\((\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+)\)', ledger)]
keys = ['log_cells','rbr_bits','qrom_work_bits','qrom_error_bits_t64','mask_m','mask_bits','rounds','stage0_agreement']
assert rows == [tuple(r[k] for k in keys) for r in d['sizes']]
assert all(r['stage0_step_vars'] == (4 if r['log_cells'] == 16 else 5 if r['log_cells'] <= 20 else 6)
           and r['stage0_queries'] == (267 if r['log_cells'] < 24 else 266) for r in d['sizes'])
assert [r[0] for r in rows] == list(range(16,29))
assert all(r['rbr_round'] == 'Query(0)' and r['qrom_terms'][1] == 129112 for r in d['sizes'])
assert d['mask_line_detail']['21']['b_cf'] == 23593235614501
assert d['mask_line_detail']['28']['b_cf'] == 379715127166310
print('13 Lean ledger rows match the Rust fixture')
PY

mkdir -p "$lane/build/Selvage"
pkgdirs=("$md"/.lake/packages/*/.lake/build/lib/lean)
export LEAN_PATH="$lane/build:$(IFS=:; echo "${pkgdirs[*]}")"
"$lean" --version
(cd "$lane/build" && "$lean" -DwarningAsError=true -R "$md" -o "$lane/build/$module.olean" "$md/$module.lean")
echo "Lean target compiled into build/$module.olean"

python3 - "$ds" "$lane/dregg_sig_zkhem_v2_selvage_xref.patch" <<'PY'
from pathlib import Path
from tempfile import TemporaryDirectory
import json, shutil, subprocess, sys
root, patch = map(Path, sys.argv[1:])
with TemporaryDirectory(prefix='w11-zkhem-patch-') as tmp:
    for name in ('agg/SECURITY.md', 'agg/src/zk_hem/v2/bounds.rs', 'agg/src/zk_hem/v2/pcs.rs', 'migrate/SECURITY.md'):
        rel = Path('crates') / name
        dst = Path(tmp) / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / rel, dst)
    args = ['git', 'apply', '--no-index']
    subprocess.run([*args, '--check', str(patch)], cwd=tmp, check=True)
    subprocess.run([*args, str(patch)], cwd=tmp, check=True)

    # Compile the isolated work methods twice, using the upstream rounding functions
    # and constants. This checks the real arithmetic without linking the upstream crate.
    rel = Path('crates/agg/src/zk_hem')
    shared = (root / rel / 'bounds.rs').read_text()
    params = (root / rel / 'v2/params.rs').read_text()
    common = next(l for l in shared.splitlines() if l.startswith('pub type MilliBits'))
    common += '\n' + next(l for l in params.splitlines() if l.startswith('pub const DIGEST_BYTES'))
    common += '\n' + shared[shared.index('pub fn log2_lo'):shared.index('/// `[CWYZ26]` interpolation inequality')]
    pcs = (root / 'crates/agg/src/pcs.rs').read_text()
    common += '\nmod pcs { ' + next(l for l in pcs.splitlines() if l.startswith('pub const MAX_PCS_NUM_VARS:')) + ' }'
    fixtures = json.loads(Path('zkhem_v2_conformance.json').read_text())['sizes']
    checks = []
    for r in fixtures:
        rem = r['log_cells'] - r['stage0_step_vars']
        checks.append('let (a, cf) = mask_line_bad_challenges(4, %d, %d);' % (rem, r['mask_m']))
        checks.append('let agree = %d; assert!(a <= agree);' % r['stage0_agreement'])
        checks.append('let pairs = johnson_list(4 << %d, agree, (1 << %d) + 1).unwrap();' % (rem, rem))
        checks.append('assert_eq!(FIELD_MILLIBITS - log2_hi(cf + pairs), %d);' % r['mask_bits'])
        checks.append('assert_eq!(query_bits(4 << %d, agree + %d, %d).unwrap() - 1000, %d);' %
                      (rem, r['stage0_step_vars'], r['stage0_queries'], r['rbr_bits']))
        checks.append('let r = Report { rbr_bits: %d, rounds: %d };' % (r['rbr_bits'], r['rounds']))
        checks.append('assert_eq!((r.qrom_work_bits(), r.classical_work_bits(), r.qrom_sum_bits(64000)), (%d,%d,%d));' %
                      (r['qrom_work_bits'], r['classical_work_bits'], r['qrom_error_bits_t64']))
    for directory, label, q, c in [(root, 'original', 128779, 198500), (Path(tmp), 'patched', 128799, 198531)]:
        bounds = (directory / rel / 'v2/bounds.rs').read_text()
        constants = '\n'.join(l for l in bounds.splitlines() if l.startswith(('const QROM_', 'pub const FIELD_MILLIBITS:')))
        mask_line = bounds[bounds.index('pub fn mask_line_bad_challenges'):bounds.index('/// `[DKT26]` Theorem 5.12 with `d = 1`')]
        methods = bounds[bounds.index('    fn digest_millibits'):bounds.index('    pub fn qrom_error_bits')]
        main = checks + [
            f'assert_eq!(Report {{ rbr_bits: 267508, rounds: 100 }}.qrom_work_bits(), {q});',
            f'assert_eq!(Report {{ rbr_bits: 200094, rounds: 100 }}.classical_work_bits(), {c});',
        ]
        source = (common + '\n' + constants + '\n' + mask_line + '\npub struct Report { rbr_bits: i64, rounds: usize }\n'
                  + 'impl Report {\n' + methods + '}\nfn main() {\n' + '\n'.join(main) + '\n}\n')
        (Path(tmp) / 'work.rs').write_text(source)
        subprocess.run(['rustc', '--edition=2024', '-Dwarnings', '-O', 'work.rs', '-o', 'work'], cwd=tmp, check=True)
        subprocess.run([str(Path(tmp) / 'work')], cwd=tmp, check=True)
        print(f'{label} upstream methods: 13 fixture rows matched, synthetic QROM {q}, classical {c}')
print('Upstream patch checked on isolated copies')
PY
echo 'All Wave 11 Lane 3 checks passed'
