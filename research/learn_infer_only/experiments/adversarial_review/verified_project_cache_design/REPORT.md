# Verified project-cache proposal

[DERIVED recommendation] After run018 succeeds, export one immutable, observed
project/object/dependency cohort from that completed run. The next integration
can copy unchanged, dependency-closed project objects from that export into its
fresh overlay, then compile changed/new modules, every reverse dependent and
all four umbrellas. Keep the existing source census, patch equality, import
boundaries and final source-stability checks. A cache failure stops reuse;
there is no fallback to the main project's cached objects.

[DERIVED scope] The export is a **new post-success byte observation**, not a
retroactive assertion that run018 hashed external dependencies before and
after compilation. Run018's original claim remains: a clean project-source
closure build using trusted cached external packages/toolchain. Future reuse
requires equality with the exported external/toolchain cohort and exact project
dependency closure. This preserves that explicit residual instead of inventing
a historical attestation. Neither a hermetic build nor hostile-OS protection
is claimed.

## What the current producer records

[SOURCE] The inspected current and archived run018 harnesses both have SHA256
`563b52272d913d00eb5751588befbbe7f7b226d83016d1c53f917dececff57ff`.
The following locations refer to those inspected bytes in
`experiments/integration/check_all_formal.py`:

| Location | Existing behavior | Cache consequence |
| --- | --- | --- |
| `Run.__init__`, lines 254–270 | Archives exact harness immediately. | Bind this copy to the successful report's input hash. |
| `Run.command`, lines 275–299 | Saves exact argv, LEAN_PATH, exit status, and each compiled source's before/after hash. | Bind each exported module to its actual successful command record. |
| `Run.finish`, lines 301–327 | Records final report, selected-input and companion-source stability. | Require final success and no changed source, HEAD or status. |
| lines 495–515 | Recomputes the four-umbrella project-source import closure in rebuild mode. | Recover and export the complete DAG; do not infer it from selected modules alone. |
| lines 525–528, 545–548 | Skips inherited project artifacts and removes the main-project olean root in rebuild mode. | Keep this prohibition when adding verified cache copies. |
| lines 550–566 | Records environment-path provenance and final per-module olean byte hashes. | Useful producer records, but not a reusable cache manifest by themselves. |

[EXECUTED read-only inspection] `run018_schema.json` retains the observation
time, available artifact hashes/schemas and one completed command-log schema.
At that observation the final `report.json` and `compiled_olean_hashes.json`
were absent: **run018 was not eligible for export yet**. Its
`cached_dependency_artifacts.json` was empty, consistent with rebuild mode.
The 77-entry `applied_source_hashes.json` covers patch outputs/support/umbrellas,
not the whole project closure. The selected `axiom_census.json` is likewise not
a full dependency DAG. No active report, source, manifest or output was edited.

[SOURCE] `environment.json` contains a saved LEAN_PATH and Lean version report;
its `sources` are research-paper inputs. It is not an external-object or
toolchain-byte inventory. The archived harness's final compiled-object map is
written only after the compilation loop completes. An after-success export
must supply the missing graph/cohort and must not label that new observation
as a historical pre/post dependency check.

## Minimal export after success

[DERIVED] Write a separate `verified_project_cache_v1/` beside the completed
results. Do not rewrite the run018 report. Publish the export manifest only
after every condition below passes; keep its digest explicit in the next run.

1. Require final `status == passed`, `rebuild_project_source_closure == true`,
   all project modules actually compiled, no inherited project objects, both
   import boundaries passed, four successful umbrella commands, exact patch
   checks, and no changed source/companion fields. Bind report, archived harness,
   archived input manifest, census, compiled-object map and each compilation
   log by hash. Match the archived harness to its recorded before/after input
   hash. A passing older selected-only run such as run017 cannot seed this cache.
2. From the preserved isolated source tree, parse the full project import graph
   with the pinned supported header parser and recompute its exact four-root
   closure. For every module, match its source bytes to the corresponding
   successful compile log's before/after hashes; match the object bytes to the
   final saved olean hash. Require graph/order/module sets to agree with the
   successful report. Export source bytes, explicit import order, direct project
   dependencies and module ownership/resolution. Reject unsupported import
   syntax, missing nodes, cycles, ambiguous resolution or unrooted selected input.
3. Copy verified project artifacts into the export as regular files. Record
   module-relative names, byte counts and hashes; reject symlinks/escapes and
   recheck copied bytes. Account for every importable sibling, including its
   absence. A `.olean`-only export is valid only when no other importable part
   is present for that module. For run018, refuse an unrecorded
   `.olean.server`, `.olean.private`, or `.ir` sibling: its producer records
   only the main `.olean` hash. A future producer can support complete bundles
   by recording each part's byte hash during compilation and at completion.
4. Observe and pin the complete ordered external artifact roots and toolchain
   byte cohort: resolved roots, member names/presence, imported-code artifacts,
   compiler binary/runtime libraries, version, platform, and effective compiler
   options/environment policy. Hashing the whole permitted external artifact
   roots plus toolchain runtime is a conservative first implementation: it also
   covers implicit Init and transitive external imports without trusting an
   incomplete external graph. Reject any root/alias reaching the main project's
   `.lake/build/lib/lean`. Bind this observation as
   `post_success_observed_trusted_external_cohort`; record it separately from
   the original producer's environment-path evidence.
5. Seal a manifest containing producer/report/harness hashes, the observed
   external/toolchain cohort digest, compiler-policy digest, complete project
   graph, source/object bundle hashes and per-module transitive input keys.
   Verify all exported bytes once more before publication. A missing/mismatched
   source, object, dependency or final report blocks that export.

[SOURCE artifact detail] Lean 4.30's local source
`Lean/Environment.lean:122` defines ModuleData imports without the source/byte
dependency attestation required here. Its `findOLeanParts` at line 2038 can
load server/private parts opportunistically; the import loader at lines
2170–2182 can load `.ir`. Therefore the saved main `.olean` digest alone must
not silently certify an unrecorded sibling bundle. At inspection run018's
current output file suffix census contained only `.olean`; the exporter must
check again after successful completion.

## Next-run admission and invalidation

[DERIVED] Add an explicit opt-in input such as
`--verified-project-cache <export-manifest> --cache-sha256 <expected-digest>`
while retaining a fresh source tree and overlay. Complete the new manifest's
source census, exact patch application and import-closure calculation before
selecting cache entries. Do not reuse the old source tree as the new build tree.

[DERIVED] Rehash the export's report/harness/module bundles and reconstruct its
transitive keys. Recompute the prospective source/import graph and current
external/toolchain cohort. Hash names and byte contents, not mtime/size alone.
Use ordered imports and explicit project/external ownership; moving a name
between those ownership sets invalidates the importing module. A conservative
key is:

```
K(m) = H(policy, cohort, module-name, source-bytes-hash, ordered-imports,
         [(dependency-name, K(dependency), saved-artifact-bundle-hashes)])
```

[DERIVED] Process the graph in topological order. Mark a module for rebuilding
if it is new, its source/imports/dependency ownership changed, its bundle/key
is missing, the compiler policy changed, or any project dependency is being
rebuilt. Always mark `Theory`, `Compiler`, `Selvage`, and `Assurance` for rebuilding;
that mark also propagates to any importer. An external/toolchain cohort change
invalidates the entire v1 cache. Do not attempt to salvage reverse dependents
merely because a rebuilt dependency happened to produce the same bytes.

[DERIVED] Before invoking Lean, copy only admitted bundles into the new isolated
overlay and rehash their destinations. Precreate real directories, not directory
symlinks. The LEAN_PATH consists of that overlay and the explicitly verified
external roots; the original project cache is absent. Audit resolution using
Lean's namespace-root rule, not a per-module fallback assumption:
`Lean/Util/Path.lean:59–71` chooses the first root containing the namespace.
Reject any import whose planned source/object ownership differs from its actual
resolved root. Compile the rebuild list in topological order, using unchanged
source guards/options. Run requested check modules afresh as before. If a
copy, hash, resolution or compile fails, stop; do not switch to ambient caches.

[DERIVED] Finalize with before/after source and external/toolchain cohort hashes,
all reused/copied/output object hashes, exact parent cache digest, rebuilt/reused
module lists and inherited guard-log links. Label this new run
`verified_project_cache`, not a clean full project rebuild. Keep the original
seed cache immutable. The minimal v1 policy does not promote newly compiled
modules from cached runs into the seed: they remain rebuilt in later runs until
a separately completed clean project build produces a new export. This avoids
introducing a recursive cache-provenance chain in the first implementation.

## Helper proposal and validation

[SOURCE / DERIVED] `cache_plan.py` is a narrow metadata planner and read-only
schema inspector. It validates completion/mode metadata, graph closure,
transitive input keys and conservative invalidation. It intentionally produces
`authorization_to_install_cache: false`: the export/current-byte and resolver
gates above belong in the integration wrapper before any installation. No
exporter, copier, Lean process or build invocation is implemented or enabled
by this proposal. Producer archived-harness identity remains separate from
compiler-policy compatibility, so adding cache orchestration alone need not
invalidate the seed; that compatibility mapping must be explicit and reviewed.

[EXECUTED] Both following standard-library commands exit zero; stdout is kept
in the named JSON files. `source_reads.json` pins the five inspected source
and environment files and retains an additional exact self-check command,
stdout, stderr and exit status; the active-run schema observation was not
repeated during finalization.

```
python3 -B research/learn_infer_only/experiments/adversarial_review/verified_project_cache_design/cache_plan.py --self-check > research/learn_infer_only/experiments/adversarial_review/verified_project_cache_design/self_check.json
python3 -B research/learn_infer_only/experiments/adversarial_review/verified_project_cache_design/cache_plan.py --inspect-run research/learn_infer_only/experiments/integration/results/run_018 > research/learn_infer_only/experiments/adversarial_review/verified_project_cache_design/run018_schema.json
```

The small metadata checks reuse two unchanged library modules while rebuilding
four umbrellas; changing their dependency rebuilds all six; changing the
environment cohort also rebuilds all six. These checks exercise plan propagation,
not Lean or an actual cache. No runtime speedup is measured or promised. Stable
project modules outside the reverse dependency closure become eligible, which
is the intended way to avoid repeating the full project compilation.

[OPEN next implementation] Wait for run018's final outcome. On success, build
and review the separate observed cohort/export, then add the gated copy/rebuild
branch to a new integration run. Current metadata is sufficient to anchor and
reconstruct the project side after success, subject to the explicit checks above;
the graph, artifact bundles, external/toolchain cohort and cache-consumption
record are new exports. No active checker, manifest, run018 file, companion,
shared ledger or stopped-task artifact was changed by this design review.
