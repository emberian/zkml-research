# Verified project cache implementation

[EXECUTED] `synthetic_results.json` retains the exact Python command, source
hashes, stdout/stderr and exit status for 31 passing tests. The fixtures contain
explicitly fake compiler identities and non-Lean object bytes. No Lean, build,
crypto or model process ran, and those fixtures make no kernel-proof claim.

[SOURCE] The separate helper is
`experiments/integration/verified_project_cache.py`. It implements the reviewed
design without editing the running/finished integration harness, manifests,
run018 records or companion trees. It never imports or executes an archived
harness, invokes a subprocess, reads `os.environ`, or installs overlay objects.
Validation uses explicit exceptions and remains active under optimized Python.

## Wrapper API

[SOURCE] All arguments are keyword-only except the single-plan recheck calls.
Pass canonical absolute `Path` objects and an explicit expected manifest digest.
Use the returned plan directly; if persisting it, retain its exact digest in the
wrapper's independently pinned launch inputs.

1. `export_completed_run(run_dir, build_dir, metadata_dir, object_dir,
   compiler_policy, expected_report_sha256, expected_harness_sha256)` is the only
   writing API. It requires an already successful clean project-source producer,
   verifies its saved command/source/object provenance, and seals a new observed
   export. The metadata and object directories must be fresh and separate from
   the producer. Large object/source copies are restricted to ignored
   `experiments/integration/build/`. Publication is manifest-last; a failure may
   retain an unsealed partial directory, which is never admissible.
2. `plan_admission(manifest_path, expected_sha256, source_root, selected_modules,
   overlay_root, compiler_policy)` rehashes the exported evidence/source/objects,
   parses the prospective source closure, observes the current explicit cohort,
   checks resolution, and returns `ordered_copies`, `ordered_rebuilds`, the full
   topological order, exact `lean_path`, cohort and parent manifest pins. It
   writes nothing. The prospective overlay must be absent or empty.
3. The wrapper creates real directories and copies **only** `ordered_copies`
   using their source/destination/pin records. It then calls
   `verify_staged_copies(plan)`. This requires exact destination bytes and exact
   directory membership; even an unexpected empty namespace directory fails.
4. The wrapper compiles `ordered_rebuilds` in the returned order using its normal
   source/command guards and the exact returned `lean_path`. It runs the selected
   source census, patch checks, import boundaries and requested controls itself.
   All four umbrellas always rebuild. A failed copy/check/compile stops the run.
5. `recheck_plan_inputs(plan)` is the requested public final cohort/source/seed
   recheck. It also derives the copy/rebuild records again and rejects changed
   plan records. `verify_final_outputs(plan)` adds exact final object/directory
   membership and unchanged copied-object hashes, returning observed output
   hashes for the wrapper's new report. It does not independently certify a
   successful compilation; the wrapper must retain those successful commands.

[DERIVED requirement] Label a consuming run `verified_project_cache`, with
separate reused/rebuilt lists and the parent manifest. Never label it another
clean full project build. v1 does not promote newly compiled outputs of cached
runs into a seed; a new seed requires a separately successful clean producer.

## Exact admission boundary

[SOURCE] The export binds the final passed report, exact archived harness and
archived input manifest, the combined patch, public source census, before/after
companion maps, applied source hashes, empty inherited-project-artifact list,
all saved successful commands, and the complete saved project object map. It
reconstructs the four-umbrella DAG from isolated sources, checks every source
against its own successful compile log's before/after hash, and every object
against its saved byte hash. The saved compile set and order must cover that
closure exactly. Original producer and copied export bytes are rechecked before
sealing. Report/hash requirements are caller-supplied explicit pins.

[SOURCE] Recursive input keys bind source bytes, ordered imports, implicit Init,
project/external resolution, policy/cohort, and every transitive project
dependency's key and saved object hash. Changed/new modules and their reverse
dependents rebuild. Any external/toolchain/policy difference invalidates all v1
reuse. Changes to dependency output bytes after export fail admission outright.

[SOURCE] The explicit policy accepts only plain `lean -o`, an empty semantic
environment override map, compiler/version/platform, ordered external roots,
the public toolchain root and forbidden project cache roots. It hashes every
file and directory membership in those explicitly selected public trees.
Absent external roots are recorded as absent; appearing later changes the
cohort. The toolchain root must exist. No ambient environment or unrelated
home-directory inventory is collected. File symlinks are accepted only within
the explicit public cohort roots, with link and resolved-content pins; directory
symlinks and forbidden project-root aliases fail.

[SOURCE] Resolution follows the first namespace root, including implicit Init.
An external module shadowed by a partial project namespace fails. Project
exports and destinations contain only saved main `.olean` files with exactly
their expected directories. Unknown/unrecorded project siblings (`.ir`,
`.olean.server`, `.olean.private`, or other files) fail before copying. The
explicit external cohort does inventory its entire artifact bundles.

## Actual run018 observation and residual

[SOURCE] `compiler_policy.json` derives ordered external roots and compiler
version from run018's saved records, plus the explicitly observed platform and
public toolchain root. Its saved LEAN_PATH includes one absent Cli artifact
root; this is retained and pinned, never silently removed. The final producer
report SHA256 is
`75c1d3921998fdf7fd5377af07be6887304ebe004369eab09c28effc75ec5b39`;
archived harness SHA256 is
`563b52272d913d00eb5751588befbbe7f7b226d83016d1c53f917dececff57ff`.

[EXECUTED] `export_run018.py` completed the authorized byte-only export with
exit zero in 301.5937797499937 seconds. `export_attempt_001.json` retains the exact
command and unchanged exporter helper pins. Its sealed
`run018_observed_001/manifest.json` has SHA256
`3c8943f716651ed9db18176f41d7197a6d919c364dda9b8c30520f42a015439f`.
The export covers 567 modules, 588 public evidence files and 1,134 ignored
source/object files totaling 504,544,196 bytes. Its 12 cohort tree observations
contain 118,998 file observations; explicit roots overlap, so this is not a
unique-file count. No real cache consumption or speedup is claimed here.

[SOURCE / EXECUTED] The executed exporter helper SHA256 is
`86c3c3305864e6c6abaa78e4bc54d548f851de122fc2ec5de2a5bf903e9cf04a`.
After that export completed, one final path-hardening check was added:
`_fresh` now explicitly requires `path.resolve() == path` before testing storage
containment. The authorized export used canonical paths and is unaffected.
Its exact old helper, tests and 30-test result remain under
`pre_hardening_001/`; no historical source pin was rewritten. The final helper
SHA256 is
`91f31c3b80f3897d394832a79e43959e2c60c1b1206ae894a3656b25de02ac07`,
with the additional noncanonical-storage test included in the 31-test result.

[DERIVED residual] This is a **new post-success observed byte cohort**. Run018
remains a clean project-source build using trusted cached external packages and
toolchain. The export cannot retroactively attest historical external-byte
stability or the ambient environment inherited by that old process. The future
wrapper must supply the declared compiler policy and retain its actual argv,
version and resolver records. Shared-OS trust, trusted compiler/metaprogram
behavior, and nonhermetic host behavior remain explicit; no hostile-OS or
arbitrary ambient-input attestation is claimed. Equality of the observed cohort
and project dependency closure is required for every reused object.

[OPEN] Root owns the successor wrapper and its actual compilation. An
independent review is being recorded separately under
`adversarial_review/verified_project_cache_review/`.
