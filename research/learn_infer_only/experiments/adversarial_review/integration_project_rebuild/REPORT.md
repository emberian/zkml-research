# Review of the isolated project-source rebuild

[DERIVED verdict, 2026-09-08] **Accepted for the pinned 952-pin preflight after
two root-owned corrections.** The reviewed checker can proceed to the declared
four-umbrella project-source rebuild. This is a source/helper review; no Lean
process, integration runner, cryptographic operation or private-state read was
performed here. A passed Lean build remains a separate executed result.

[EXECUTED final pins]

| Input | SHA-256 |
| --- | --- |
| `experiments/integration/check_all_formal.py` | `563b52272d913d00eb5751588befbbe7f7b226d83016d1c53f917dececff57ff` |
| `experiments/integration/modules_overnight_sampled.json` | `abb61812f05441be74f02450f6ebe9449d729c805cd28714210a74e556c96c79` |
| `formal/integration/overnight_sampled_umbrella_wiring.patch` | `65c223f0513ea9e4ae89226c89b09e1988f023e0ca098e3bcfadf199a1232b53` |
| This review's `result.json` | `2cfb51a98a9e6dcb45ea2415f30578ba97b59bca059c755c7c121e957b6cf2b3` |
| This review's `source_manifest.json` | `70d7d372bac09ac1768bbad24b3568ac786296eafd4ae416ca28cd1e6f48fa12` |

[EXECUTED reproduction] From the repository root:

```sh
python3 -B research/learn_infer_only/experiments/adversarial_review/integration_project_rebuild/audit.py
```

[EXECUTED scope] `audit_006.stdout` and the empty `audit_006.stderr` retain the
final successful execution. `commands.json` records only read-only companion
Git queries and `git init/apply --check/apply` inside this review's ignored
scratch directory. The script never calls `Run`, `integrate` or Lean. It writes
only this review directory. `source_manifest.json` pins 641 public source,
manifest, report and local parser-source inputs. Network, Kagi and Scry queries:
zero. Companion HEAD, Git status and all 524 source hashes were unchanged.

## Findings corrected before acceptance

[EXECUTED initial blocking finding] The original 952-pin manifest selected
`Selvage.BabyBearFullUD` and `Selvage.FullUDSamplingBudget`, but neither was
reachable from the staged umbrellas. Their patches added source files only;
the earlier wiring rooted `FullUDFriConsumer` and `FullUDWitnesses`. The helper
reported exactly those two missing modules. The integration checker itself
would reject them at its selected-rooting check before compilation.

[SOURCE / EXECUTED correction] Root added a separate zero-pin manifest lane
whose new patch imports `Selvage.FullUDSamplingBudget` from `Selvage.lean`.
Its existing imports reach `BabyBearFullUD` transitively. The original core
wiring remains unchanged. Final traversal has no unrooted selected module.

[EXECUTED initial parser limitation] The intermediate `imports` helper silently
returned no imports for `public import Theory.A` and an `import` keyword followed
by a newline. Neither form occurs in the current 596-source corpus, but silent
omission was unsuitable for a reused closure instrument.

[SOURCE / EXECUTED correction] At `check_all_formal.py:98`, root now detects
prefixed import commands and rejects unsupported forms. The final controls
reject public-import, newline-after-import and quoted-name examples. A same-line
two-name input and one with nested/intervening comments both return the two
names. These are helper controls, not claims that every accepted token sequence
is valid Lean syntax. The tool remains a restricted lexical importer; the Lean
parser and compilation are authoritative. Pinned local
`Lean/Parser/Module/Syntax.lean` and `Lean/Parser/Module.lean` supplied the
primary syntax reference; no network source was needed.

## Exact current import closure

[EXECUTED] Git's `ls-files --cached --others --exclude-standard '*.lean'` returns
524 companion source files. The selected manifest adds 72 new modules with
exactly 952 theorem pins. All 596 resulting sources agree with an independent
header scanner for the actual headers present. The staged four umbrellas root
567 modules: 495 existing project modules and all 72 proposed modules. Every
project dependency precedes its dependent in the computed topological order.

[DERIVED scope] The 29 existing sources outside these four umbrellas are listed
in `result.json`: they include the Kernel/Pred/Effects umbrellas and modules,
the top-level Minidregg umbrella, several unrelated compiler modules and script
entry points. The intended claim is therefore **the complete current source
closure of the four staged umbrellas**, not all 524 baseline files and not a
clean rebuild of external dependencies. The checker's retained
`no_clean_full_build_claim` flag is consistent with that narrower scope.

[EXECUTED cache resolution] The recorded environment contains the original
project olean root, ten package roots and the pinned Lean toolchain root. The
rebuild branch removes the resolved original project root, leaving eleven
absolute external roots. All 145 distinct external direct imports in this
closure have an existing olean in those roots. No available project module name
has a same-name olean in any retained root, and no resolved external import
points back into the original project artifact tree.

[SOURCE isolation] `integrate` begins at `check_all_formal.py:330`. In rebuild
mode its artifact-walk body breaks before creating any project file symlink.
The new overlay starts empty, and `LEAN_PATH` is replaced with that overlay
followed by the filtered external roots. Each compile writes its `-o` output
inside the research scratch overlay, rejects symlink outputs and checks the
resolved destination remains within the scratch tree. Its working directory
is the copied research source tree. The original companion is used only for
source copies, read-only metadata and the existing boundary script.

[EXECUTED current path premises] The integration/build and companion/artifact
directories are regular directories; none of the 524 baseline Lean files is a
symlink. `LEAN_PATH`, `LEAN_SYSROOT`, `LEAN_SRC_PATH` and `ELAN_TOOLCHAIN` were
unset in the review environment. This check covers the recorded current paths;
it is not a sandbox for arbitrary changed manifests or dependency code.

[SOURCE / DERIVED existing generated-file effects] The current rooted project
contains existing `#eval` conformance and renderer commands. The review traced
their writers and literal targets: `prover/testdata/`, `prover/generated/` and
`prover/src/` paths, including the current dirty
`Compiler/UwueavePreoProjectionV2.lean` generator. These relative targets resolve
inside the fresh research source working directory. Generic writer definitions
are not themselves executed merely by being defined. The observed exhibit-only
commands print/check in-memory values. No project source was rewritten to
suppress existing evaluation commands. `result.json` retains the token scan and
target inventory; this review did not execute those commands.

## Census, patch bytes and run017 provenance

[EXECUTED archive recovery] Run017 originally retained the checker hash but no
checker copy. After this review reported the gap, root recovered the earlier
bytes by reversing the subsequent recorded edits. The recovered file hashes
exactly to the independently retained run017 input hash
`42d9ba6f2b064d8d2896e5c7d02f2732019388f1d13e82fddf1a78b1258b45b9`.
The separate `harness_archive_recovery.json` names that method; this is not
described as an original contemporaneous copy. The new checker archives its
own bytes in `Run.__init__` and the exact manifest bytes at integration start.

[EXECUTED comparison] `checker_vs_run017.diff` and the AST comparison identify
changes only in `imports`, `Run`, `integrate` and `main`. The private declaration
census, comment/string masking and EOF patch helper are AST-identical to the
recovered run017 versions. All 70 selected modules common with run017 match
its applied-source hashes exactly. All 524 baseline source hashes also match
run017; no proof-body edit or census relaxation was used for this preflight.

[SOURCE / EXECUTED private-name check] `census` at `check_all_formal.py:149`
matches a printed `_private.<exact module>.<counter>.<qualified declaration>`
only to a source declaration marked private. The actual printed name remains
inside its exact Lean message guard; public declarations cannot use the
exception. The inspected FullUDTeeth source has six theorem pins, three private.
Controls reject a wrong module, a public declaration borrowing a private print,
a private declaration with a public print, a missing private guard, a proof
placeholder and a nonallowed axiom. The optional generic module-name argument
is not used by integration: each selected destination supplies its exact name.

[EXECUTED exact application] Every selected source matches the new-file bytes
in its lane patch, and all 72 selected sources round-trip through the checker's
text representation without newline conversion. A bounded combined helper
patch applies inside this review's scratch tree to exactly 77 expected files:
72 modules, four staged umbrellas and one license. Every resulting file matches
the expected raw bytes, not merely normalized text. The helper patch's ordering
is review-local; its SHA is not claimed as the later integration runner's patch.

[EXECUTED license / EOF] The Apache license is 11,356 bytes, has no final newline,
and retains SHA-256
`c5accbbd8546e94c34aed24afe689a617627d18eed5a6c48277e48db57c23851`
after actual patch application. `unified_patch` at `check_all_formal.py:43`
adds the conventional patch EOF marker to incomplete diff lines without adding
a byte to the file. Six further bounded Git-application controls cover adding,
removing and retaining a final newline, empty baseline files and Unicode. All
resulting bytes match. The accepted exact-byte statement is for the inspected
UTF-8/LF inputs; arbitrary new source encodings need their own review.

[EXECUTED retained attempts] Audits001–002 stop at the initial rooting gap;
003–004 retain the other helper results while reporting those unrooted modules.
Audit005 stops because root changed the checker during its read window; it does
not replace the last stable results. Audit006 succeeds against the final pins.
No full Lean build was used to repair or conceal an earlier result.

[OPEN next] Root owns the full source-closure launch and its independent outcome.
Any later manifest, including a proposed additional execution-proof package,
requires its own rooting/pin preflight. This review does not approve its semantic
claims or prestate its compile result.
